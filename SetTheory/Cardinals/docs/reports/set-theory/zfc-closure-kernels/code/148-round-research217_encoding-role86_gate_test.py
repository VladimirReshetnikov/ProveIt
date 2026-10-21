"""Owned role86 source rotation prefix test, supported CI1 actions only."""
from pathlib import Path
import sys,json,time,collections,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
sys.path.insert(0,str(ROOT/'research218_round2_encoding'));from compose_rho_nop import subst,flatten
T=A.R.table(A.NEW/'k218.native.tm');old=A.P.tree(json.load(open(A.NEW/'sites218.json')));groups,paths,gates=A.P.allocation(T,old)
n=next(iter(groups[86]));a,(b,c)=n;assert a in groups[90] and b==c==('CI',1)
new,occ=subst(old,n,((a,b),c));ss=flatten(new)
assert (a,b)in groups[150] and A.continuation_cfg(old)==A.continuation_cfg(new)
actions=sorted({act for op,bit,act,p in gates if op==('CI',1)and bit==1});assert len(actions)<=10
start=time.monotonic();steps=0
class Cap(Exception):pass

def allocation(U,t):
 out=collections.defaultdict(set);pm={};gg=[];entry150=[]
 def walk(n,p):
  global steps
  if A.P.leaf(n):return
  tape={-1:1,**{i:int(b)for i,b in enumerate(p)}};initial=tape.copy();q=84;h=0;seen=set();trace=[]
  while h!=len(p):
   if q==254 or h not in tape:raise ValueError(('unknown prefix',p,q,h,trace[-8:]))
   key=(q,h,tuple(tape.items()))
   if key in seen:raise ValueError(('cycle',p,q,h))
   seen.add(key)
   if steps>=100000 or time.monotonic()-start>=2:raise Cap('aggregate cap')
   bit=tape[h];w,d,z=U[q,bit];trace.append([q,h,bit,w,d,z]);tape[h]=w;h+=d;q=z;steps+=1
  if tape!=initial:raise ValueError(('dirty prefix',p,q,trace[-8:]))
  out[q].add(n);pm[p]=q
  if q==150:entry150.append(dict(path=p,predecessor=p[-1:]or None,subtree_leaves=A.length(n)))
  for bit,ch in enumerate(n):
   if A.P.leaf(ch):gg.append((ch,bit,U[q,bit],p+str(bit)))
   else:walk(ch,p+str(bit))
 walk(t,'');return out,pm,gg,entry150
reports=[]
for action in actions:
 U=T.copy();U[86,0]=(0,1,150);U[86,1]=action
 helperkeys=[(188,1),(189,1),(190,0),(190,1),(156,1),(176,1)];assert all(U[k]==T[k]for k in helperkeys)
 rec=dict(action=list(action),states=len(U)//2,changes=[dict(state=86,read=b,old=T[86,b],new=U[86,b])for b in(0,1)])
 try:
  ng,np,gg,en=allocation(U,new);oldg=collections.defaultdict(set)
  for op,b,act,p in gates:oldg[op,b].add(act)
  rec.update(status='PREFIX_PASS',novel_primitive_gates=[dict(op=op,read=b,action=act,path=p)for op,b,act,p in gg if act not in oldg[op,b]],entry150=en,new_roles={str(q):[A.length(x)for x in ns-groups.get(q,set())]for q,ns in ng.items()if ns-groups.get(q,set())})
 except Cap as e:rec.update(status='CAP_UNKNOWN',reason=str(e));reports.append(rec);break
 except Exception as e:rec.update(status='PREFIX_REJECT',reason=repr(e))
 reports.append(rec)
rec=dict(source_sha256=hashlib.sha256(A.compact(ss)).hexdigest(),exact_ordinal_cfg=True,global_occurrences=occ,source_nodes=len(A.P.nodes(new))+23,table_states=218,actions_considered=len(reports),actions_available=len(actions),reports=reports,transitions=steps,seconds=time.monotonic()-start,scope='Literal exact prefix/gate test only. Shared arithmetic roles remain outside this check; failed prefix is not a whole-runtime counterexample.')
(OUT/'ROLE86_GATE_TEST.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
