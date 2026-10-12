"""Independent complete-atlas replay. Does not import the producer.

Leaves enumerate edge cut sets; joins solve signed equations by graph traversal.
Exact equality with recomputed tables checks omitted states as well as soundness.
The source grammar is a graph recipe, NOT a geometric provenance certificate.
"""
from __future__ import annotations
from itertools import combinations, product
import json
from typing import Any

class VerificationError(ValueError): pass

def fail(message: str) -> None: raise VerificationError(message)

def exact_equal(a: Any,b: Any) -> bool:
    # Typed structural comparison avoids decimal conversion of binary integers.
    todo=[(a,b)]
    while todo:
        x,y=todo.pop()
        if type(x) is not type(y): return False
        if isinstance(x,dict):
            if set(x)!=set(y): return False
            todo.extend((x[k],y[k]) for k in x)
        elif isinstance(x,(list,tuple)):
            if len(x)!=len(y): return False
            todo.extend(zip(x,y))
        elif x!=y: return False
    return True

def exchange(a: int,b: int) -> int:
    return [0,2,1,3][a] if b else a

def partition(values: list[int]) -> list[int]:
    first={}; result=[]
    for x in values:
        if x not in first: first[x]=len(first)
        result.append(first[x])
    return result

def components(n: int, constraints: list[tuple[int,int,int]]) -> tuple[list[int],list[int]] | None:
    adj=[[] for _ in range(n)]
    for u,v,b in constraints:
        adj[u].append((v,b)); adj[v].append((u,b))
    owner=[-1]*n; color=[0]*n; nc=0
    for root in range(n):
        if owner[root]>=0: continue
        owner[root]=nc; queue=[root]
        for u in queue:
            for v,b in adj[u]:
                expected=color[u]^b
                if owner[v]<0: owner[v]=nc; color[v]=expected; queue.append(v)
                elif color[v]!=expected: return None
        nc+=1
    return owner,color

def validate_source(g: Any) -> None:
    if not isinstance(g,dict) or set(g)!={"k","nodes"}: fail("bad grammar fields")
    if type(g["k"]) is not int or g["k"]<0: fail("bad threshold")
    if not isinstance(g["nodes"],list) or not g["nodes"]: fail("empty node list")
    widths=[]
    for i,z in enumerate(g["nodes"]):
        if not isinstance(z,dict): fail("bad rule")
        if z.get("op")=="leaf":
            if set(z)!={"op","vertices","edges","terminals"}: fail("bad leaf fields")
            vs=z["vertices"]; es=z["edges"]; ts=z["terminals"]
            if not isinstance(vs,list) or any(type(v) is not int or v!=j for j,v in enumerate(vs)): fail("unlisted vertices")
            if not isinstance(es,list) or not isinstance(ts,list): fail("bad leaf inventory")
            n=len(vs)
            if any(type(v) is not int or not 0<=v<n for v in ts) or len(set(ts))!=len(ts): fail("bad leaf terminals")
            for edge in es:
                if not isinstance(edge,list) or len(edge)!=3: fail("bad edge record")
                u,v,w=edge
                if any(type(t) is not int or not 0<=t<n for t in (u,v)) or type(w) is not int or w<1: fail("bad weighted edge")
            widths.append(len(ts))
        elif z.get("op") in ("join","map"):
            if set(z)!={"op","children","maps","keep"}: fail("bad internal fields")
            ch=z["children"]; maps=z["maps"]; keep=z["keep"]; arity=2 if z["op"]=="join" else 1
            if not isinstance(ch,list) or len(ch)!=arity or any(type(c) is not int or not 0<=c<i for c in ch): fail("non-acyclic rule")
            if not isinstance(maps,list) or len(maps)!=arity: fail("bad map count")
            labels=[]
            for c,mp in zip(ch,maps):
                if not isinstance(mp,list) or len(mp)!=widths[c] or any(type(v) is not int or v<0 for v in mp): fail("bad map")
                labels+=mp
            q=len(set(labels))
            if set(labels)!=set(range(q)): fail("bad quotient namespace")
            if not isinstance(keep,list) or any(type(v) is not int or not 0<=v<q for v in keep) or len(set(keep))!=len(keep): fail("bad retained terminals")
            widths.append(len(keep))
        else: fail("unknown operation")

def leaf_meta(z: dict) -> dict:
    n=len(z["vertices"]); es=z["edges"]; ts=z["terminals"]
    sol=components(n,[(u,v,0) for u,v,_ in es]); assert sol is not None
    own,_=sol; degree=[0]*n
    for u,v,_ in es: degree[u]+=1; degree[v]+=1
    return {"part":partition([own[t] for t in ts]),"vertices":n,"edges":len(es),
            "hidden_components":len(set(own)-{own[t] for t in ts}),
            "degrees":[min(4,degree[t]) for t in ts],
            "private_cubic":all(degree[v]==3 for v in range(n) if v not in ts)}

def internal_layout(z: dict, metas: list[dict], rows: tuple | None=None):
    q=len(set(v for mp in z["maps"] for v in mp)); eq=[]
    for a,(m,mp) in enumerate(zip(metas,z["maps"])):
        first={}
        for j,c in enumerate(m["part"]):
            if c not in first: first[c]=j
            p=0 if rows is None else (rows[a][1]>>j)&1
            eq.append((mp[first[c]],mp[j],p))
    return components(q,eq)

def internal_meta(z: dict, ms: list[dict]) -> dict:
    layout=internal_layout(z,ms); assert layout is not None
    own,_=layout; q=len(own); ds=[0]*q; keep=z["keep"]
    for m,mp in zip(ms,z["maps"]):
        for j,v in enumerate(mp): ds[v]+=m["degrees"][j]
    return {"part":partition([own[v] for v in keep]),
            "vertices":sum(m["vertices"]-len(mp) for m,mp in zip(ms,z["maps"]))+q,
            "edges":sum(m["edges"] for m in ms),
            "hidden_components":sum(m["hidden_components"] for m in ms)+len(set(own)-{own[v] for v in keep}),
            "degrees":[min(4,ds[v]) for v in keep],
            "private_cubic":all(m["private_cubic"] for m in ms) and all(ds[v]==3 for v in range(q) if v not in keep)}

def collapse_flags(fixed: int, tags: list[int]) -> list[int]:
    possible=[False]*4; possible[fixed]=True
    for tag in tags:
        new=[False]*4
        for a in range(4):
            if possible[a]: new[a|tag]=True; new[a|exchange(tag,1)]=True
        possible=new
    return [a for a in range(4) if possible[a]]

def leaf_from_cut(z: dict, cut: tuple[int,...]):
    n=len(z["vertices"]); es=z["edges"]; ts=z["terminals"]; chosen=set(cut)
    sol=components(n,[(u,v,int(j in chosen)) for j,(u,v,_) in enumerate(es)])
    if sol is None: return set()
    own,x=sol; tags={c:0 for c in set(own)}
    for j,(u,v,_) in enumerate(es):
        if j not in chosen: tags[own[u]] |= 1<<x[u]
    roots={}; visible=[]; p=0
    for j,t in enumerate(ts):
        c=own[t]
        if c not in roots: roots[c]=x[t]; visible.append(c)
        p|=(x[t]^roots[c])<<j
    vt=tuple(exchange(tags[c],roots[c]) for c in visible)
    d=sum(es[j][2] for j in cut)
    return {(d,p,vt,h) for h in collapse_flags(0,[tags[c] for c in tags if c not in roots])}

def internal_rows(z: dict, ms: list[dict], rows: tuple):
    sol=internal_layout(z,ms,rows)
    if sol is None: return set()
    own,x=sol; marks={c:0 for c in set(own)}; fixed=0
    for row,m,mp in zip(rows,ms,z["maps"]):
        fixed |= row[3]; first={}
        for j,c in enumerate(m["part"]):
            if c not in first:
                first[c]=j; marks[own[mp[j]]] |= exchange(row[2][c],x[mp[j]])
    roots={}; vis=[]; p=0
    for j,t in enumerate(z["keep"]):
        c=own[t]
        if c not in roots: roots[c]=x[t]; vis.append(c)
        p|=(x[t]^roots[c])<<j
    tags=tuple(exchange(marks[c],roots[c]) for c in vis)
    return {(sum(row[0] for row in rows),p,tags,h) for h in collapse_flags(fixed,[marks[c] for c in marks if c not in roots])}

def read_row(row: Any, meta: dict, k: int):
    if not isinstance(row,list) or len(row)!=4 or not isinstance(row[2],list): fail("invalid row shape")
    d,p,tags,h=row; r=len(meta["part"]); c=max(meta["part"],default=-1)+1
    if type(d) is not int or not 0<=d<=k or type(p) is not int or not 0<=p<1<<r or type(h) is not int or not 0<=h<4: fail("invalid row range")
    if len(tags)!=c or any(type(t) is not int or not 0<=t<4 for t in tags): fail("invalid component tags")
    for j,c in enumerate(meta["part"]):
        if j==meta["part"].index(c) and (p>>j)&1: fail("noncanonical root parity")
    return d,p,tuple(tags),h

def verify_packet(packet: Any, expected_grammar: dict | None=None, *, work_limit: int | None=None) -> dict:
    if not isinstance(packet,dict) or packet.get("schema")!="component-gauge-cut-atlas-v1": fail("wrong schema")
    g=packet.get("grammar"); validate_source(g)
    if expected_grammar is not None and not exact_equal(g,expected_grammar): fail("source binding mismatch")
    tables=packet.get("atlases")
    if not isinstance(tables,list) or len(tables)!=len(g["nodes"]): fail("missing atlas")
    k=g["k"]; metadata=[]; checked=[]; work=0
    def tick():
        nonlocal work
        work+=1
        if work_limit is not None and work>work_limit: fail("replay budget exhausted; inconclusive")
    for i,z in enumerate(g["nodes"]):
        record=tables[i]
        if not isinstance(record,dict) or set(record)!={"metadata","rows","origins"}: fail("bad atlas record")
        if z["op"]=="leaf": meta=leaf_meta(z)
        else: meta=internal_meta(z,[metadata[j] for j in z["children"]])
        if not exact_equal(record["metadata"],meta): fail("forged metadata")
        if not isinstance(record["rows"],list): fail("missing row list")
        rows=[read_row(r,meta,k) for r in record["rows"]]
        if rows!=sorted(set(rows)): fail("duplicate or unordered atlas rows")
        expected=set()
        if z["op"]=="leaf":
            m=len(z["edges"])
            for a in range(min(k,m)+1):
                for cut in combinations(range(m),a):
                    tick()
                    if sum(z["edges"][e][2] for e in cut)<=k: expected.update(leaf_from_cut(z,cut))
        else:
            ch=z["children"]; ms=[metadata[j] for j in ch]
            # Independently indexed exact degree, same proved shared-budget principle.
            choices=[{} for _ in ch]
            for buckets,j in zip(choices,ch):
                for row in checked[j]: buckets.setdefault(row[0],[]).append(row)
            for degrees in product(*(sorted(b) for b in choices)):
                if sum(degrees)>k: continue
                for rs in product(*(choices[a][d] for a,d in enumerate(degrees))):
                    tick(); expected.update(internal_rows(z,ms,rs))
        if set(rows)!=expected: fail(f"incomplete or incorrect atlas at rule {i}")
        origins=record["origins"]
        if not isinstance(origins,list) or len(origins)!=len(rows): fail("missing derivation")
        for row,origin in zip(rows,origins):
            if not isinstance(origin,dict): fail("bad origin")
            if z["op"]=="leaf":
                if set(origin)!={"cut_edges"}: fail("bad leaf origin")
                cut=origin["cut_edges"]
                if not isinstance(cut,list) or any(type(e) is not int or not 0<=e<len(z["edges"]) for e in cut) or cut!=sorted(set(cut)): fail("bad cut edge indices")
                if row not in leaf_from_cut(z,tuple(cut)): fail("wrong leaf cut witness")
            else:
                if set(origin)!={"child_rows"}: fail("bad internal origin")
                inds=origin["child_rows"]; ch=z["children"]
                if not isinstance(inds,list) or len(inds)!=len(ch) or any(type(a) is not int or not 0<=a<len(checked[j]) for a,j in zip(inds,ch)): fail("bad child witness")
                rs=tuple(checked[j][a] for a,j in zip(inds,ch))
                if row not in internal_rows(z,[metadata[j] for j in ch],rs): fail("wrong composition witness")
        metadata.append(meta); checked.append(rows)
    if metadata[-1]["part"]: query={"status":"OPEN_INTERFACE"}
    else:
        costs=[r[0] for r in checked[-1] if r[3]==3]
        query={"status":"MARKED_CUT" if costs else "NO_MARKED_CUT","minimum_cost":min(costs) if costs else None,
               "scope":"abstract graph query only; no knot verdict"}
    if not exact_equal(packet.get("query"),query): fail("forged root query")
    return {"verified":True,"rules":len(checked),"rows":sum(map(len,checked)),
            "replay_candidate_work":work,"query":query}

def verify_coloring_recipe(recipe: Any, expected_grammar: dict | None=None) -> dict:
    """Soundness-only, independent symbolic-coloring verifier; no atlas needed.

Checks a coloring family for every assignment of the root component bits.
This positive witness does NOT certify absence or minimum cut cost.
"""
    if not isinstance(recipe,dict) or set(recipe)!={'schema','grammar','records','root'} or recipe['schema']!='component-gauge-coloring-v1':fail('bad coloring schema')
    g=recipe['grammar'];validate_source(g)
    if expected_grammar is not None and not exact_equal(g,expected_grammar):fail('coloring source mismatch')
    meta=[]
    for z in g['nodes']:
        meta.append(leaf_meta(z) if z['op']=='leaf' else internal_meta(z,[meta[j] for j in z['children']]))
    records=recipe['records'];done=[]
    if not isinstance(records,list) or not records:fail('empty coloring proof')
    def expr(e,c):
        if not isinstance(e,list) or len(e)!=2 or type(e[0]) is not int or not -1<=e[0]<c or type(e[1]) is not int or e[1] not in (0,1):fail('bad symbolic color')
        return e[0],e[1]
    for rid,rec in enumerate(records):
        if not isinstance(rec,dict) or type(rec.get('node')) is not int or not 0<=rec['node']<len(meta):fail('bad recipe node')
        node=rec['node'];z=g['nodes'][node];m=meta[node];row=read_row(rec.get('row'),m,g['k']);c=len(row[2])
        marks=[0]*c;hidden=0;cost=0
        if z['op']=='leaf':
            if set(rec)!={'node','row','colors'} or not isinstance(rec['colors'],list) or len(rec['colors'])!=len(z['vertices']):fail('bad leaf coloring')
            expressions=[expr(e,c) for e in rec['colors']]
            sol=components(len(z['vertices']),[(u,v,0) for u,v,_ in z['edges']]);assert sol is not None
            own,_=sol;visible={own[t]:m['part'][j] for j,t in enumerate(z['terminals'])}
            for v,(var,b) in enumerate(expressions):
                if var!=visible.get(own[v],-1):fail('wrong component gauge variable')
            for j,t in enumerate(z['terminals']):
                if expressions[t]!=(m['part'][j],(row[1]>>j)&1):fail('wrong symbolic boundary')
            for u,v,w in z['edges']:
                var,a=expressions[u];var2,b=expressions[v]
                if var!=var2:fail('edge crosses independent gauge variables')
                if a!=b:cost+=w
                elif var<0:hidden|=1<<a
                else:marks[var]|=1<<a
        else:
            if set(rec)!={'node','row','children','transports'}:fail('bad internal coloring fields')
            ids=rec['children'];trs=rec['transports'];ch=z['children']
            if not isinstance(ids,list) or len(ids)!=len(ch) or any(type(j) is not int or not 0<=j<rid for j in ids):fail('cyclic coloring proof')
            if not isinstance(trs,list) or len(trs)!=len(ch):fail('bad coloring transports')
            cms=[meta[j] for j in ch];layout=internal_layout(z,cms);assert layout is not None
            own,_=layout;active={own[t]:m['part'][j] for j,t in enumerate(z['keep'])};values={}
            for a,(child_id,j,mp) in enumerate(zip(ids,ch,z['maps'])):
                childnode,cr=done[child_id]
                if childnode!=j:fail('wrong child recipe binding')
                if not isinstance(trs[a],list) or len(trs[a])!=len(cr[2]):fail('bad transport arity')
                trans=[expr(e,c) for e in trs[a]];cost+=cr[0];hidden|=cr[3];seen=set()
                for t,cc in enumerate(cms[a]['part']):
                    var,b=trans[cc];expectvar=active.get(own[mp[t]],-1)
                    if var!=expectvar:fail('wrong transport owner')
                    value=(var,b^((cr[1]>>t)&1))
                    if mp[t] in values and values[mp[t]]!=value:fail('inconsistent symbolic quotient')
                    values[mp[t]]=value
                    if cc not in seen:
                        seen.add(cc);mask=exchange(cr[2][cc],b)
                        if var<0:hidden|=mask
                        else:marks[var]|=mask
            for j,t in enumerate(z['keep']):
                if values[t]!=(m['part'][j],(row[1]>>j)&1):fail('wrong parent symbolic colors')
        if (cost,tuple(marks),hidden)!=(row[0],row[2],row[3]):fail('incorrect symbolic cost or exact flags')
        done.append((node,row))
    root=recipe['root']
    if type(root) is not int or not 0<=root<len(done) or done[root][0]!=len(g['nodes'])-1:fail('bad recipe root')
    return {'verified':True,'records':len(records),'root_row':list(done[root][1]),
            'scope':'positive coloring family; not an absence or minimality certificate'}
