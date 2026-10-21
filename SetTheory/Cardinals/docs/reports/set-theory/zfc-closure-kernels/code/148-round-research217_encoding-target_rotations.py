"""Owned exact source rotations and conservative contextual alias tests."""
from pathlib import Path
import sys,json,time,collections
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
sys.path.insert(0,str(ROOT/'research218_round2_encoding'));from compose_rho_nop import subst,flatten
T=A.R.table(A.NEW/'k218.native.tm');src=A.P.tree(json.load(open(A.NEW/'sites218.json')));groups,paths,gates=A.P.allocation(T,src)
nodeqs=collections.defaultdict(list)
for q,ns in groups.items():
 for n in ns:nodeqs[n].append(q)
oldgates=collections.defaultdict(set)
for op,b,act,p in gates:oldgates[op,b].add(act)
start=time.monotonic();steps=0

def alias(U,entry,forbid,p,b,target):
 global steps
 q=entry;h=len(p);ones={-1}|{i for i,c in enumerate(p)if c=='1'}
 if b:ones.add(h)
 orig=ones.copy();seen=set();trace=[]
 for k in range(33):
  if k and q==target and h==len(p)+1 and ones==orig:return dict(status='PASS',steps=k,trace=trace)
  if q==forbid:return dict(status='FORBIDDEN_ROLE')
  if q==254:return dict(status='HALT')
  if h>len(p):return dict(status='OPAQUE_EXIT',state=q,head=h,trace=trace)
  key=q,h,frozenset(ones)
  if key in seen:return dict(status='CYCLE')
  seen.add(key)
  if k==32:return dict(status='FUEL_UNKNOWN')
  if steps>=30000 or time.monotonic()-start>=5:raise TimeoutError('aggregate cap')
  bit=int(h in ones);w,d,z=U[q,bit];trace.append([q,h,bit,w,d,z])
  if w:ones.add(h)
  else:ones.discard(h)
  q=z;h+=d;steps+=1

def main():
 reports=[]
 for q,size in[(200,206),(157,56)]:
  n=next(n for n in groups[q]if A.length(n)==size);a=n[0];b,c=n[1];assert all(A.boundary(x)==(0,0,False)for x in(a,b,c));new=(a,b),c
  changed,occ=subst(src,n,new);ns=flatten(changed);assert A.continuation_cfg(src)==A.continuation_cfg(changed)
  targets=[nodeqs[ch]for ch in new];assert all(len(x)==1 for x in targets);targets=[x[0]for x in targets]
  U=T.copy();U[q,0]=(0,1,targets[0]);U[q,1]=(1,1,targets[1])
  rec=dict(state=q,old_subtree_leaves=size,occurrences=occ,new_child_entries=targets,source_dag_nodes=len(A.P.nodes(changed))+len({(op,arg)for p,op,arg in ns}),exact_cfg=True,raw_states=len(U)//2)
  out=OUT/f'rotate_{q}';out.mkdir(exist_ok=True);(out/'sites.json').write_bytes(A.compact(ns));(out/'raw.native.tm').write_bytes(A.P.M.enc(U))
  try:
   ng,np,gg=A.P.allocation(U,changed);bad=[dict(op=op,read=b,entry=act,path=p)for op,b,act,p in gg if act not in oldgates[op,b]]
   rec.update(prefix_walks_complete=True,novel_primitive_entry_count=len(bad),first_novel_primitive_entries=bad[:6])
   # Known baseline subtree entries are semantic labels, not proof that a new
   # predecessor context realizes them; expose any new logical role per state.
   extra={str(s):[A.length(n)for n in nn-groups.get(s,set())]for s,nn in ng.items()if nn-groups.get(s,set())}
   rec['new_or_changed_state_roles']=extra
  except Exception as e:rec.update(prefix_walks_complete=False,prefix_error=repr(e))
  if q==200:
   ps=[p for p,s in paths.items()if s==q];survivors=[];rejects=[]
   for entry in sorted({s for s,b in U}-{q}):
    for p in ps:
     for b in(0,1):
      r=alias(U,entry,q,p,b,targets[b])
      if r['status']!='PASS':break
     else:continue
     break
    else:survivors.append(entry);continue
    rejects.append(dict(entry=entry,first_case=[p,b],result=r))
   rec['role_alias_survivors']=survivors;rec['role_alias_rejections']=rejects
  reports.append(rec)
 data=dict(reports=reports,helper_transitions=steps,seconds=time.monotonic()-start,scope='Exact CFG rotations; raw physical patches are provisional. Prefix errors/novel primitive entries are diagnosis, not full-runtime counterexamples. Alias screen uses complete known source prefixes, positive progress and exact child boundary; unknown right exterior is never guessed.')
 (OUT/'TARGET_ROTATION_RESULTS.json').write_text(json.dumps(data,indent=2)+'\n')
 print(json.dumps({**{k:v for k,v in data.items()if k!='reports'},'reports':[{k:v for k,v in r.items()if k not in('new_or_changed_state_roles','role_alias_rejections')}for r in reports]},indent=2))
if __name__=='__main__':main()
