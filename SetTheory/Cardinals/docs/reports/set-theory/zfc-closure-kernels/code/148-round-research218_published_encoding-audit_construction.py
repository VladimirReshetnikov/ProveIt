"""Independent owned audit of published218 source transport and local merge.
Supplied programs are never imported. All external inputs are literal data.
"""
from pathlib import Path
import sys,json,hashlib
from functools import lru_cache
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
BASE=ROOT/'latest219_baseline/candidate-k219';NEW=ROOT/'latest218_baseline/candidate-k218'
sys.path.insert(0,str(ROOT/'research218_encoding'));import price_sources as P
sys.path.insert(0,str(ROOT/'research218_round2_encoding'));from reassociate_four_increments import cfg as address_cfg
from compose_rho_nop import flatten
sys.path.insert(0,str(ROOT/'k223_merged_runtime_audit/runtime'));import independent_runtime as R

def H(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def compact(x):return(json.dumps(x,separators=(',',':'))+'\n').encode()
@lru_cache(None)
def length(t):return 1 if P.leaf(t)else length(t[0])+length(t[1])
@lru_cache(None)
def boundary(t):
 if P.leaf(t):
  op,a=t;return(1,0,False)if op=='CD'else(a,0,False)if op=='CB'else(0,a,False)if op=='CC'else(0,0,op=='CH')
 a,b=boundary(t[0]),boundary(t[1]);return(max(max(a[0]-1,0),b[0]),max(a[1],max(b[1]-1,0)),a[2]or b[2])
def continuation_cfg(t):
 N=length(t);out=[]
 def walk(n,start,breaks,continues):
  if P.leaf(n):
   op,k=n;after=(start+1)%N
   target=lambda stack,k:stack[-k]%N if len(stack)>=k else 0
   edges=[]if op=='CH'else[target(continues,k)]if op=='CC'else[target(breaks,k)]if op=='CB'else[target(breaks,1),after]if op=='CD'else[after]
   assert len(out)==start;out.append([op,None if op in('CB','CC')else k,edges]);return
  end=start+length(n);middle=start+length(n[0]);walk(n[0],start,breaks+[end],continues);walk(n[1],middle,breaks,continues+[start])
 walk(t,0,[],[]);return out

def at(t,p):
 for c in p:t=t[int(c)]
 return t

def replace(t,p,n):
 if not p:return n
 b=int(p[0]);return(tuple(replace(t[i],p[1:],n)if i==b else t[i]for i in(0,1)))

def local(T,q,h,tape,target,limit=8):
 original=tape.copy();trace=[]
 for unused in range(limit):
  if trace and(q,h)==target:
   assert tape==original;return trace
  assert h in tape and q!=254
  b=tape[h];w,d,z=T[q,b];trace.append([q,h,b,w,d,z]);tape[h]=w;h+=d;q=z
 raise AssertionError(('local proof did not close',q,h,target))

def main():
 paths=[BASE/'k219.native.tm',BASE/'sites219.json',NEW/'k218.native.tm',NEW/'sites218.json',NEW/'code/data/source205.dag.json',NEW/'code/data/rotation_paths.json',NEW/'code/data/stage219_patch.json']
 pins={str(p.relative_to(ROOT)):H(p)for p in paths}
 oldsites=json.load(open(BASE/'sites219.json'));old=P.tree(oldsites);newsites=json.load(open(NEW/'sites218.json'));new=P.tree(newsites)
 dag=json.load(open(NEW/'code/data/source205.dag.json'));nodes=[]
 for i,row in enumerate(dag['nodes']):
  if row[0]=='leaf':assert len(row)==3;nodes.append(tuple(row[1:]))
  else:assert row[0]=='pair'and len(row)==3 and all(type(j)is int and 0<=j<i for j in row[1:]);nodes.append((nodes[row[1]],nodes[row[2]]))
 assert len(nodes)==len(set(nodes))==205;stage=nodes[dag['root']];assert len(P.nodes(stage))+len({(op,a)for p,op,a in flatten(stage)})==205
 rotations=json.load(open(NEW/'code/data/rotation_paths.json'));assert len(rotations)==len(set(rotations))==5
 assert all(not p.startswith(q)for p in rotations for q in rotations if p!=q)
 rebuilt=stage;rotation_receipts=[]
 for p in rotations:
  n=at(rebuilt,p);assert not P.leaf(n)and not P.leaf(n[0]);a,b=n[0];c=n[1]
  assert[length(x)for x in(a,b,c)]==[26,19,7]and all(boundary(x)==(0,0,False)for x in(a,b,c))
  rebuilt=replace(rebuilt,p,(a,(b,c)));rotation_receipts.append(dict(path=p,factor_leaves=[26,19,7],boundaries=[boundary(x)for x in(a,b,c)]))
 assert rebuilt==new and flatten(new)==newsites
 reference=None;metrics={}
 for name,t,s in[('accepted219',old,oldsites),('stage205',stage,flatten(stage)),('published218',new,newsites)]:
  assert[r[1:]for r in s]==[r[1:]for r in oldsites]
  address=address_cfg(s);continuation=continuation_cfg(t);assert address==continuation
  if reference is None:reference=address
  else:assert address==reference
  metrics[name]=dict(leaves=len(s),dag_nodes=len(P.nodes(t))+len({(op,a)for p,op,a in s}),internal_subtrees=len(P.nodes(t)),depth=max(len(p)for p,op,a in s),edges=sum(len(e[2])for e in address),source_sha256=hashlib.sha256(compact(s)).hexdigest())
 B=R.table(BASE/'k219.native.tm');M=R.table(NEW/'k218.native.tm');S=B.copy();patch=json.load(open(NEW/'code/data/stage219_patch.json'));seen=set()
 for e in patch:
  row=e['state'],e['read'];assert row not in seen and S[row]==tuple(e['old']);seen.add(row);S[row]=tuple(e['new'])
 U=S.copy();assert U[188,0]==(0,1,165)and U[188,1]==(1,1,20);U[188,0]=(0,1,166);U[188,1]=(1,1,12)
 assert U[85,0]==U[212,0]==(0,1,98)and U[85,1]==(1,1,12)and U[212,1]==(1,1,150)
 assert[(r,a)for r,a in U.items()if a[2]==85]==[((155,0),(0,1,85))]
 assert[(r,a)for r,a in U.items()if a[2]==212]==[((177,1),(1,1,212))]
 built={r:a for r,a in U.items()if r[0]!=212};built[177,1]=(1,1,85);built[85,1]=(1,-1,190);assert built==M
 assert 0 not in(85,212)and 254 not in(85,212)
 local_cases=[]
 for marker,oldq in[(0,85),(1,212)]:
  for b in(0,1):
   w,d,z=U[oldq,b];assert w==b and d==1
   trace=local(M,85,0,{-1:marker,0:b},(z,1));assert len(trace)==(1 if b==0 else 3 if marker==0 else 5)
   local_cases.append(dict(old_state=oldq,marker=marker,read=b,old_duration=1,new_duration=len(trace),trace=trace,exact_two_cell_patch=True))
 allocation={}
 for name,T,t in[('stage219',S,stage),('unfolded219',U,new),('published218',M,new)]:
  groups,pp,gates=P.allocation(T,t);allocation[name]=dict(physical_states=len(T)//2,decoder_states=len(groups),source_roles=sum(map(len,groups.values())),all_known_source_prefixes_restored=True,primitive_occurrences=len(gates))
 working={q for q,b in M};reach={0};work=[0]
 for q in work:
  for b in(0,1):
   z=M[q,b][2]
   if z!=254 and z not in reach:reach.add(z);work.append(z)
 assert working==reach and len(working)==218 and all(z!=212 for w,d,z in M.values())
 delta=[dict(row=r,old=B[r],new=a)for r,a in sorted(M.items())if B[r]!=a];assert len(delta)==32 and{q for q,b in B}-working=={212}
 out=dict(status='PASS',input_pins=pins,source_metrics=metrics,rotations=rotation_receipts,changed_primitive_addresses=sum(a[0]!=b[0]for a,b in zip(flatten(stage),newsites)),stage_patch_rows=len(patch),allocation=allocation,retained_delta=delta,local_fold=local_cases,all_tape_fold_scope='All initial tapes from designated state0. Unique incoming writes establish predecessor marker; each old step expands to a nonempty1/3/5-step exact whole-tape block, with no interior halt. This is not all-tape equivalence of the reallocated source stage to accepted219.',runtime_scope='Primitive contracts and blank startup are separate independent audits.',graph_reachable_states=len(reach))
 assert out['changed_primitive_addresses']==260
 (OUT/'CONSTRUCTION_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');(OUT/'stage205.sites.json').write_bytes(compact(flatten(stage)));(OUT/'stage219.native.tm').write_bytes(P.M.enc(S));(OUT/'unfolded219.native.tm').write_bytes(P.M.enc(U))
 print(json.dumps({k:v for k,v in out.items()if k not in('input_pins','retained_delta','local_fold')},indent=2))
if __name__=='__main__':main()
