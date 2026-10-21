"""Reuse old subtrees only in decoder-compatible contexts; keep old rows intact.

Exploratory prefix binding only. This is not a primitive-runtime proof.
"""
from pathlib import Path
from collections import defaultdict,Counter
from functools import cache
import argparse,sys,json,time
sys.dont_write_bytecode=True
ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
ap.add_argument('--repo',type=Path,required=True)
ap.add_argument('--table',type=Path,required=True);args=ap.parse_args()
base=args.repo/'Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(base/'k218-quantifier-stability/pricing'))
import source_language as s,build221 as b
seed=base/'candidate-k218'
old=s.tree(json.loads((seed/'sites218.json').read_text()))
new=s.tree(json.loads(args.source.read_text()))
T=b.read_table(args.table.read_bytes());groups,_=b.decoder_map(T,old)
states=defaultdict(set)
for q,ns in groups.items():
    for n in ns:states[n].add(q)
counter=Counter();rejected=[]

@cache
def old_compatible(n,p,q):
    counter['compatibility_calls']+=1
    if q not in states[n]:return False
    for bit in (0,1):
        if s.leaf(n[bit]):continue
        tape={i:int(v)for i,v in enumerate(p+str(bit))};tape[-1]=1
        before=dict(tape);h=len(p);state=q
        for tick in range(100):
            if h==len(p)+1:break
            if h not in tape:return False
            w,d,state=T[state,tape[h]];tape[h]=w;h+=d
        if h!=len(p)+1 or tape!=before:return False
        if not old_compatible(n[bit],p+str(bit),state):return False
    return True

leaf_actions={}
for op in ('CI','CD','CC','CB','CH'):
    for arg in ([None]if op=='CH'else range(10)):
        leaf=op,arg
        for bit in (0,1):
            choices=Counter(T[q,bit]for n,qs in states.items()for q in qs if n[bit]==leaf)
            direct=[row for row in choices if row[:2]==(bit,1)]
            if len(direct)==1:leaf_actions[leaf,bit]=direct[0]
            elif leaf==('CC',1)and bit==1:leaf_actions[leaf,bit]=(0,-1,1)
            elif leaf==('CC',2)and bit==1:leaf_actions[leaf,bit]=(0,-1,16)
            elif leaf==('CB',1)and bit==1:leaf_actions[leaf,bit]=(0,-1,40)

U=dict(T);fresh0=max(300,max(q for q,_ in T)+1);fresh=fresh0;by_actions={};assignments=[];used_old=Counter()
def go(n,p):
    global fresh
    assert not s.leaf(n)
    for q in sorted(states[n]):
        if q!=84 and old_compatible(n,p,q):
            used_old[q]+=1;return q
    if states[n]:
        rejected.append({'prefix':p,'states':sorted(states[n]),'leaf_count':len(s.sites(n))})
    rows=tuple(leaf_actions[n[bit],bit]if s.leaf(n[bit])else(bit,1,go(n[bit],p+str(bit)))for bit in(0,1))
    if rows in by_actions:return by_actions[rows]
    q=fresh;fresh+=1;by_actions[rows]=q
    U[q,0],U[q,1]=rows
    assignments.append({'state':q,'prefix':p,'rows':rows})
    return q

started=time.monotonic();out={'scope':'Exact decoder prefix validation only; no primitive runtime or startup check.'}
try:
    for bit in(0,1):
        U[84,bit]=leaf_actions[new[bit],bit]if s.leaf(new[bit])else(bit,1,go(new[bit],str(bit)))
    reach={0};todo=[0]
    for q in todo:
        for bit in(0,1):
            z=U[q,bit][2]
            if z!=254 and z not in reach:reach.add(z);todo.append(z)
    U={k:v for k,v in U.items()if k[0]in reach}
    gg,_=b.decoder_map(U,new)
    for q,ns in gg.items():
        if q in groups and q!=84:
            assert ns<=groups[q],('old binding',q)
    assert all(U[q,bit]==T[q,bit]for q in reach if q<fresh0 and q!=84 for bit in(0,1))
    if new==old: assert U==T, 'Identity allocation changed the baseline table'
    out.update(status='CONTEXT_AWARE_PREFIX_PASS',identity_control=(U==T) if new==old else None,working_states=len(U)//2,
        fresh=fresh-fresh0,retired=sorted({q for q,_ in T}-reach),used_old=dict(used_old),
        assignments=assignments,rejected_old_placements=rejected,counts=dict(counter))
    args.output.mkdir(exist_ok=False)
    (args.output/'prefix-only.tm').write_bytes(b.table_bytes(U))
except (ValueError,AssertionError,KeyError)as e:
    args.output.mkdir(exist_ok=False)
    out.update(status='REJECTED',error=repr(e),assignments=assignments,rejected_old_placements=rejected,counts=dict(counter))
out['seconds']=time.monotonic()-started
(args.output/'result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k not in ('assignments','rejected_old_placements','used_old')}))
