#!/usr/bin/env python3
"""Reconstruct the K215 partial-selector / local-field-reader composition.

Only Python's standard library is required. No solver, optimizer, or runtime
search is used. The ordinary source-calibration and binary-runtime proofs are
separate from this finite, exact construction. Source parsing and closed-splice
operations follow the cited K216 Permuted Commands package.
"""
from pathlib import Path
from functools import cache
import argparse, hashlib, json

HERE=Path(__file__).resolve().parent
REFERENCE_PIN='8b5dc46f10d927b2db5e4bcb522d482779ec61c72c82717d7bf12fca3550a3bc'

def require(ok,message):
    if not ok: raise ValueError(message)

def sha(raw): return hashlib.sha256(raw).hexdigest()
def leaf(t): return isinstance(t[0],str)
def sites(t,p=''):
    return [(p,*t)] if leaf(t) else sites(t[0],p+'0')+sites(t[1],p+'1')
def compact(rows): return (json.dumps(rows,separators=(',',':'))+'\n').encode()

def parse(rows):
    trie={}
    for p,op,r in rows:
        require(op in ('CI','CD','CB','CC','CH'),'Unknown primitive')
        require(r is None if op=='CH' else type(r)is int and r>=0,'Bad primitive argument')
        node=trie
        for bit in p:
            require(bit in '01' and 'leaf' not in node,'Malformed source prefix')
            node=node.setdefault(bit,{})
        require(not node,'Duplicate or intersecting source address')
        node['leaf']=(op,r)
    def finish(node):
        if 'leaf'in node:
            require(set(node)=={'leaf'},'Source leaf has descendants')
            return node['leaf']
        require(set(node)=={'0','1'},'Incomplete binary source')
        return finish(node['0']),finish(node['1'])
    t=finish(trie)
    require([list(row)for row in sites(t)]==rows,'Noncanonical source order')
    return t

@cache
def width(t): return 1 if leaf(t) else width(t[0])+width(t[1])
@cache
def boundary(t):
    if leaf(t):
        op,r=t
        if op=='CD':return 1,0
        if op=='CB':return r,0
        if op=='CC':return 0,r
        return 0,0
    a,b=boundary(t[0]),boundary(t[1])
    return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)

def seq(xs):return xs[0]if len(xs)==1 else(xs[0],seq(xs[1:]))
def extract(t,start,end):
    chunks=[]
    def walk(q,lo=0):
        hi=lo+width(q)
        if hi<=start or end<=lo:return
        if start<=lo and hi<=end:
            require(boundary(q)==(0,0),'Extraction factor is not closed')
            chunks.append(q);return
        require(not leaf(q),'Extraction cuts a primitive')
        walk(q[0],lo);walk(q[1],lo+width(q[0]))
    walk(t)
    require(sum(map(width,chunks))==end-start,'Extraction size mismatch')
    return seq(chunks)

def splice_closed(t,edits):
    used={}
    def walk(q,lo=0):
        hi=lo+width(q)
        touched=[(rg,repl)for rg,repl in edits.items()if not(hi<=rg[0]or rg[1]<=lo)]
        if not touched:return q
        for(start,end),repl in touched:
            if start<=lo and hi<=end:
                require(boundary(q)==(0,0),'Splice deletes an open factor')
                if lo==start:
                    used[start,end]=used.get((start,end),0)+1
                    return repl
                return None
        require(not leaf(q),'Splice intersects a primitive')
        left,right=walk(q[0],lo),walk(q[1],lo+width(q[0]))
        if left is None:
            require(right is None or boundary(right)==(0,0),'Deletion exposes an open right factor')
            return right
        if right is None:
            require(boundary(left)==(0,0),'Deletion exposes an open left factor')
            return left
        return left,right
    result=walk(t)
    require(used=={rg:1 for rg in edits},'Splice usage mismatch')
    return result

def at(t,p):
    for bit in p:t=t[int(bit)]
    return t
def permute(t,permutation=(2,1,0)):
    body_paths=('111','110101','110100101')
    bodies=[at(t,p)for p in body_paths]
    require([width(q)for q in bodies]==[106,26,26],'Command body sizes')
    require(all(boundary(q)==(0,0)for q in bodies),'Open command body')
    changes=dict(zip(body_paths,(bodies[i]for i in permutation)))
    def walk(q,p=''):
        if p in changes:return changes[p]
        return q if leaf(q)else(walk(q[0],p+'0'),walk(q[1],p+'1'))
    return walk(t)

def graph(t):
    count=width(t);result=[]
    def target(stack,k):return stack[k-1]if k<=len(stack)else 0
    def walk(q,i,breaks,continues):
        if leaf(q):
            op,r=q;nxt=(i+1)%count
            if op=='CI':dest=(nxt,)
            elif op=='CD':dest=(target(breaks,1),nxt)
            elif op=='CB':dest=(target(breaks,r),)
            elif op=='CC':dest=(target(continues,r),)
            else:dest=()
            result.append((op,r if op in('CI','CD','CH')else None,dest));return
        walk(q[0],i,((i+width(q))%count,)+breaks,continues)
        walk(q[1],i+width(q[0]),breaks,(i,)+continues)
    walk(t,0,(),());return result

def metrics(t):
    seen=set()
    def walk(q):
        if q in seen:return
        seen.add(q)
        if not leaf(q):walk(q[0]);walk(q[1])
    walk(t);rows=sites(t)
    return {'distinct_subtrees':len(seen),'primitive_occurrences':len(rows),
            'guarded_cases':sum(2 if op=='CD'else 1 for p,op,r in rows),
            'maximum_depth':max(len(p)for p,op,r in rows),
            'maximum_zero_run':max(len(z)for p,op,r in rows for z in p.split('1'))}

def table(raw):
    result={};starts=[]
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]));continue
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        require((q,b)not in result and b in(0,1)and w in(0,1)and d in('L','R'),'Bad table row')
        result[q,b]=(w,1 if d=='R'else-1,z)
    require(starts==[0],'Native start must be zero')
    return result
def table_bytes(t,halt=None):
    header='#! start 0\n'+(''if halt is None else f'#! halt {halt}\n')
    return(header+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--parent-table',type=Path,required=True)
    ap.add_argument('--parent-source',type=Path,required=True)
    ap.add_argument('--reference-sites',type=Path,required=True,help='Primary K216 Permuted Commands source sites')
    ap.add_argument('--recipe',type=Path,default=HERE/'k215_transition_recipe.json')
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();require(__debug__,'Assertions must be enabled')
    recipe=json.loads(a.recipe.read_text());oldraw=a.parent_table.read_bytes();srcraw=a.parent_source.read_bytes();refraw=a.reference_sites.read_bytes()
    require(sha(oldraw)==recipe['parent_native_sha256'],'Wrong Partial Selector parent table')
    require(sha(srcraw)==recipe['parent_source_sha256'],'Wrong Partial Selector parent source')
    require(sha(refraw)==REFERENCE_PIN,'Wrong Permuted Commands reference source')
    old=parse(json.loads(srcraw));read_d=extract(old,23,37);load_d=extract(old,40,66)
    walk11,transfer3=read_d
    require([width(walk11),width(transfer3),width(load_d)]==[11,3,26],'Read/load factor sizes')
    require(all(boundary(q)==(0,0)for q in(walk11,transfer3,load_d)),'Read/load association factors')
    read_load=(walk11,(transfer3,load_d))
    moved=splice_closed(old,{(23,37):None,(187,201):None,(228,254):read_load,(4659,4685):read_load})
    new=permute(moved);newrows=sites(new);newraw=compact(newrows)
    require(sha(newraw)==recipe['candidate_source_sha256'],'Source reconstruction mismatch')
    reference=parse(json.loads(refraw))
    require([r[1:]for r in newrows]==[r[1:]for r in sites(reference)],'Primitive word mismatch')
    require(graph(new)==graph(reference),'Guarded source control-flow mismatch')
    m=metrics(new)
    require(m=={'distinct_subtrees':202,'primitive_occurrences':4751,'guarded_cases':6176,'maximum_depth':47,'maximum_zero_run':6},'Unexpected source metrics')
    T=table(oldraw);oldstates={q for q,b in T};seen=set()
    for row in recipe['rows']:
        key=row['state'],row['read'];require(key not in seen,'Duplicate recipe row');seen.add(key)
        before=None if row['old']is None else tuple(row['old'])
        require(T.get(key)==before,f'Wrong recipe precondition at {key}')
        if row['new']is None:del T[key]
        else:T[key]=tuple(row['new'])
    raw=table_bytes(T);require(sha(raw)==recipe['candidate_native_sha256'],'Native table reconstruction mismatch')
    states={q for q,b in T};require(len(states)==215 and len(T)==430,'State/row census')
    require(all((q,b)in T for q in states for b in(0,1)),'Partial working table')
    require(sorted(oldstates-states)==[224]and states<=oldstates,'Deleted-state census')
    require({z for w,d,z in T.values()}-states=={254},'Unique halt convention')
    reach={0};todo=[0]
    for q in todo:
        for b in(0,1):
            z=T[q,b][2]
            if z!=254 and z not in reach:reach.add(z);todo.append(z)
    require(reach==states,'Unreachable working state')
    mapping={q:i for i,q in enumerate(sorted(states))};mapping[254]=215
    dense={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in T.items()};dense_raw=table_bytes(dense,215)
    inv={v:k for k,v in mapping.items()}
    require({(inv[q],b):(w,d,inv[z])for(q,b),(w,d,z)in dense.items()}==T,'Relabeling mismatch')
    a.output.mkdir(parents=True,exist_ok=True)
    (a.output/'k215.native.tm').write_bytes(raw);(a.output/'k215.tm').write_bytes(dense_raw);(a.output/'sites215.json').write_bytes(newraw)
    dump(a.output/'canonicalization.json',{'native_to_canonical':mapping,'canonical_to_native':inv,'native_sha256':sha(raw),'canonical_sha256':sha(dense_raw),'native_dispatcher':84,'canonical_dispatcher':mapping[84],'native_halt':254,'canonical_halt':215})
    receipt={'status':'EXACT_K215_CONSTRUCTION_AND_SOURCE_BISIMULATION_PASS','working_states':215,'transition_rows':430,'changed_retained_rows':recipe['retained_rows_changed'],'deleted_states':[224],'native_sha256':sha(raw),'canonical_sha256':sha(dense_raw),'source_sha256':sha(newraw),'reference_source_sha256':sha(refraw),'source_metrics':m,'literal_primitive_word_equal':True,'all_guarded_source_edges_equal':True,'scope':'Finite exact reconstruction, graph isomorphism and source bisimulation. Exact blank startup, source consistency calibration and universal binary runtime are separate proof obligations.'}
    dump(a.output/'reconstruction.json',receipt);print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
