#!/usr/bin/env python3
"""Rebuild PA194J from pinned PA194, and prove its finite source invariant.

Standard library only; no network, compiler package, or proof assistant needed.
This is an executable finite certificate, not a Lean/Rocq kernel theorem.
"""
from pathlib import Path
import hashlib,json,re,sys

ROOT=Path(__file__).resolve().parent
INPUT=ROOT/'inputs';OUT=ROOT/'machine';EVIDENCE=ROOT/'evidence'
NAME='pa194j'
START,HALT=74,254
PHYSICAL=[6,2,0,4,3,7,8,5,1]
EXPECTED_NATIVE='31abf450ba25066c8ac3aad6e7eedb59386b770bb4917f006800145ebb622218'

def digest(data):return hashlib.sha256(data).hexdigest()
def dump(path,data):path.write_text(json.dumps(data,indent=2)+'\n')
def parse(path):
    rows={}
    for line in path.read_text().splitlines():
        if not line.strip():continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        assert (q,b) not in rows and b in(0,1) and w in(0,1) and d in('L','R')
        rows[q,b]=(w,d,n)
    return rows
def tabletext(rows):
    return ''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(rows.items()))
def original_nodes():
    nodes={}
    for line in (INPUT/'Program.lean').read_text().splitlines():
        m=re.match(r'def (\w+) : Tree := \.node (.*)',line)
        if not m:continue
        tokens=re.findall(r'\(\.leaf \(\.(\w+)(?: (\d+))?\)\)|\b((?:node|x)\d+)\b',m[2])
        children=[name if name else ('leaf',op,int(arg) if arg else None)for op,arg,name in tokens]
        assert len(children)==2
        nodes[m[1]]=tuple(children)
    return nodes
def grammar():
    g=json.loads((INPUT/'pa194.grammar.json').read_text())
    def expand(x):
        if isinstance(x,list):return tuple(x)
        if x in g['rules']:return tuple(expand(y)for y in g['rules'][x])
        return x
    return expand(g['root'])
def replace_final_break(t):
    if t==('leaf','breakTo',1):return ('leaf','dec',4),1
    if isinstance(t,tuple) and len(t)==2:
        a,ca=replace_final_break(t[0]);b,cb=replace_final_break(t[1]);return (a,b),ca+cb
    return t,0
def source(nodes,ax):
    sites=[]
    def walk(t,p):
        if isinstance(t,str):return walk(ax if t=='x67' else nodes[t],p)
        if t[0]=='leaf':sites.append([p,t[1],t[2]]);return
        walk(t[0],p+'0');walk(t[1],p+'1')
    walk('node172','')
    bypath={p:i for i,(p,op,arg)in enumerate(sites)}
    assert len(bypath)==len(sites)
    def locate(p):
        if p in bypath:return bypath[p]
        for i,(q,op,arg)in enumerate(sites):
            if q.startswith(p)or(p.startswith(q)and'1'not in p[len(q):]):return i
        raise AssertionError(('unresolved address',p))
    def after(p):
        i=p.rfind('0');assert i>=0;return locate(p[:i]+'1')
    def cut(p,bit,k):
        for i in range(len(p)-1,-1,-1):
            if p[i]==bit:
                k-=1
                if not k:return p[:i]
        raise AssertionError(('invalid structured jump',p,bit,k))
    instructions=[]
    for p,op,arg in sites:
        if op=='inc':z=['inc',arg,after(p)]
        elif op=='dec':z=['dec',arg,after(cut(p,'0',1)),after(p)]
        elif op=='breakTo':z=['jump',after(cut(p,'0',arg))]
        elif op=='continueTo':z=['jump',locate(cut(p,'1',arg))]
        elif op=='halt':z=['halt']
        else:raise AssertionError(op)
        instructions.append(z)
    return sites,instructions

def succ(code,pc,mask):
    z=code[pc]
    if z[0]=='jump':return [(z[1],mask)]
    if z[0]=='inc':return [(z[2],mask|(1<<z[1]))]
    if z[0]=='dec':
        bit=1<<z[1]
        return [(z[3],mask&~bit),(z[3],mask)]if mask&bit else[(z[2],mask)]
    assert z[0]=='halt';return []
def closure(code):
    seen={(25,1)};todo=list(seen)
    for pc,m in todo:
        for x in succ(code,pc,m):
            assert 0<=x[0]<len(code) and 0<=x[1]<512
            if x not in seen:seen.add(x);todo.append(x)
    return seen

def check_fold(raw,folded):
    a,b=41,330
    incoming={a:set(),b:set()}
    for (q,bit),(w,d,n)in raw.items():
        if n in incoming:incoming[n].add((w,d))
    assert incoming=={41:{(0,'R')},330:{(1,'R')}}
    results=[]
    for old,history in((a,0),(b,1)):
        for bit in(0,1):
            w,d,n=raw[old,bit];target=(b if n==a else n,1 if d=='R'else-1,{-1:history,0:w})
            q,head,tape=b,0,{-1:history,0:bit};trace=[]
            for k in range(1,21):
                assert head in(-1,0)
                w,d,q=folded[q,tape[head]];tape[head]=w;head+=1 if d=='R'else-1
                trace.append([q,head,tape[-1],tape[0]])
                if(q,head,tape)==target:break
            else:raise AssertionError(('fold failed',old,bit))
            results.append({'old':old,'history':history,'bit':bit,'steps':k,'trace':trace})
    return results

def build():
    assert __debug__ and not sys.flags.optimize,'Run without -O.'
    OUT.mkdir(exist_ok=True);EVIDENCE.mkdir(exist_ok=True)
    parent_bytes=(INPUT/'pa194.native.tm').read_bytes()
    assert digest(parent_bytes)=='e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
    rows=parse(INPUT/'pa194.native.tm')
    # Published Combined controller, then the published symmetric Shift.
    combined={(164,1):(1,'R',130),(38,0):(0,'R',11),(38,1):(1,'R',122),
              (214,0):(0,'R',312),(214,1):(1,'R',20),(312,0):(0,'R',188)}
    rows.update(combined)
    rows.update({(214,1):(1,'R',30),(310,1):(1,'R',330),
                 (330,0):(0,'R',63),(330,1):(1,'L',73)})
    raw=dict(rows)
    # Published four-case fold: remove41, retain330, helper states31 and46.
    acts=[(0,'L',31),(1,'L',46)]
    rows={(q,bit):(w,d,330 if n==41 else n)for(q,bit),act in raw.items()if q!=41
          for w,d,n in[acts[bit]if q==330 else act]}
    cases=check_fold(raw,rows)
    # Ten source-level zero-test substitutions, in three physical rows.
    zero_edits={(27,1):(1,'R',21),(103,1):(1,'R',17),(2066,1):(1,'R',144)}
    rows.update(zero_edits)
    native=tabletext(rows);assert digest(native.encode())==EXPECTED_NATIVE
    controls={q for q,b in rows}
    assert len(controls)==194 and len(rows)==388 and HALT not in controls
    assert {n for w,d,n in rows.values()}-controls=={HALT}
    order=[START];index={START:0}
    for q in order:
        for bit in(0,1):
            n=rows[q,bit][2]
            if n!=HALT and n not in index:index[n]=len(order);order.append(n)
    assert len(order)==194
    dense={(index[q],bit):(w,d,194 if n==HALT else index[n])for(q,bit),(w,d,n)in rows.items()}
    nodes=original_nodes()
    nodes['node163']=('node6','node147')
    nodes['node170']=(('node36',('node167','node145')),'node56')
    nodes['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
    ax=grammar();oldsites,old=source(nodes,ax)
    assert old==json.loads((INPUT/'pa194CS.instructions.json').read_text())
    nodes['node22']=(('leaf','dec',8),('leaf','dec',6))
    nodes['node1']=('node0',('leaf','dec',3))
    ax,count=replace_final_break(ax);assert count==1
    sites,new=source(nodes,ax)
    assert len(new)==len(old)==3646
    changed=[i for i in range(len(old))if old[i]!=new[i]]
    assert changed==[3,9,26,3526,3532,3544,3550,3553,3627,3633]
    for i in changed:
        assert old[i][0]=='jump' and new[i][0]=='dec'
        assert new[i][2:]==[old[i][1],i+1]
    # Recompute both invariant closures from the actual generated programs.
    r0,r1=closure(old),closure(new)
    assert r0==r1 and len(r0)==263180 and(25,1)in r0
    assert all(succ(old,pc,m)==succ(new,pc,m)for pc,m in r0)
    assert all(x in r0 for pc,m in r0 for x in succ(old,pc,m))
    invariants=[]
    for i in changed:
        masks=sorted(m for pc,m in r0 if pc==i);r=new[i][1]
        assert masks and all(not m>>r&1 for m in masks)
        invariants.append({'site':i,'register':r,'masks':masks,'before':old[i],'after':new[i]})
    (OUT/(NAME+'.native.tm')).write_text(native)
    (OUT/(NAME+'.tm')).write_text(tabletext(dense))
    for suffix,data in[('sites',sites),('instructions',new),('labels',order+[HALT])]:dump(OUT/(NAME+'.'+suffix+'.json'),data)
    dump(EVIDENCE/'fold_cases.json',cases)
    dump(EVIDENCE/'zero_invariant.json',{'pairs':len(r0),'same_old_new_closure':True,
        'same_abstract_successors':True,'closed':True,'seed':[25,1],'changed_sites':invariants,
        'sha256':digest(json.dumps(sorted(r0),separators=(',',':')).encode())})
    receipt={'name':NAME,'working_states':194,'transitions':388,'source_sites':3646,
        'source_contracts':4755,'source_changes':changed,'positivity_pairs':len(r0),
        'native_sha256':digest(native.encode()),'dense_sha256':digest(tabletext(dense).encode()),
        'proof_scope':'Finite source invariant and exact construction; independent_verify.py verifies complete physical simulation and blank startup.',
        'kernel_checked':False}
    dump(EVIDENCE/'build_receipt.json',receipt)
    return receipt

if __name__=='__main__':print(json.dumps(build(),indent=2))
