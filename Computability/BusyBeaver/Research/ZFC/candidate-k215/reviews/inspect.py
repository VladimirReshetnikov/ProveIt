#!/usr/bin/env python3
"""Own source-tree/CFG/literal-table comparisons; no supplied import or TM simulation."""
from pathlib import Path
import json,hashlib
P=Path('/tmp/k216-permuted-partial-composition');D=Path('/tmp/zfc-intake197/extracted/K216_Permuted_Commands_2026-10-21');A=Path('/tmp/zfc-intake195/extracted/K216_Partial_Selector_2026-10-20');O=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def rows(p):return json.loads(p.read_text())
def tree(rr):
 d={p:(op,k)for p,op,k in rr};assert len(d)==len(rr)
 def walk(p=''):
  return d[p] if p in d else (walk(p+'0'),walk(p+'1'))
 return walk()
leaf=lambda t:isinstance(t[0],str)
def width(t):return 1 if leaf(t) else width(t[0])+width(t[1])
def metrics(t):
 nodes=set();lengths=[];intervals={}
 def go(n,p='',i=0):
  nodes.add(n);intervals[i,i+width(n)]=(p,n)
  if leaf(n):lengths.append(p)
  else:go(n[0],p+'0',i);go(n[1],p+'1',i+width(n[0]))
 go(t);return dict(dag=len(nodes),leaves=len(lengths),depth=max(map(len,lengths)),zero=max(len(x)for p in lengths for x in p.split('1'))),intervals

def cfg(rr):
 intervals={}
 for i,(p,op,k)in enumerate(rr):
  for j in range(len(p)+1):
   a=p[:j]
   if a not in intervals:intervals[a]=[i,i+1]
   else:intervals[a][1]=i+1
 n=len(rr);out=[]
 def exit(p,bit,k):
  for j in range(len(p)-1,-1,-1):
   if p[j]==bit:
    k-=1
    if k==0:return intervals[p[:j]][1 if bit=='0' else 0]%n
  return 0
 for i,(p,op,k) in enumerate(rr):
  dest=((i+1)%n,) if op=='CI' else (exit(p,'0',1),(i+1)%n) if op=='CD' else (exit(p,'0',k),) if op=='CB' else (exit(p,'1',k),) if op=='CC' else ()
  out.append((op,k if op in ('CI','CD') else None,dest))
 return out

def table(p):
 t={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z));assert (q,b)not in t;t[q,b]=(w,d,z)
 states={q for q,b in t};assert set(t)=={(q,b)for q in states for b in(0,1)} and {z for w,d,z in t.values()}-states=={254};return t
rr=rows(P/'sites-210.json');ref=rows(D/'machine/sites216.json');old=rows(A/'source/sites216.json')
t=tree(rr);ot=tree(old);met,iv=metrics(t);_,oi=metrics(ot)
assert[r[1:]for r in rr]==[r[1:]for r in ref] and cfg(rr)==cfg(ref)
assert met==dict(dag=202,leaves=4751,depth=47,zero=6)
assert sum(len(x[2])for x in cfg(rr))==6175 and sum(op=='CH'for p,op,k in rr)==1
assert iv[398,4572][1]==oi[412,4586][1]
N=table(P/'allocation210-run2/candidate.native.tm');T=table(A/'machine/k216.native.tm')
assert len(N)==430;removed=sorted({q for q,b in T}-{q for q,b in N});assert removed==[224]
changes=[[*k,*N[k]]for k in sorted(N)if N[k]!=T[k]];assert len(changes)==35
record=rows(P/'allocation210-run2/allocation.json');assert record['status']=='PREFIX_FAIL'and len(record['binding_failures'])==8
needrows={(69,0):(0,'L',213),(69,1):(1,'R',31),(213,0):(0,'R',92),(213,1):(1,'R',90),(92,0):(0,'R',104),(90,0):(0,'R',105),(164,0):(0,'L',201),(164,1):(1,'R',98),(201,0):(0,'R',195),(201,1):(1,'R',196),(195,0):(0,'R',150),(196,0):(0,'R',77),(81,0):(0,'L',111),(111,0):(0,'R',104),(111,1):(1,'R',128),(104,0):(0,'R',123),(128,0):(0,'R',21),(108,1):(0,'L',10),(10,0):(0,'L',16),(16,1):(0,'L',1)}
assert all(N[k]==v for k,v in needrows.items())
incoming={q:[[s,b,*v]for(s,b),v in sorted(N.items())if v[2]==q]for q in (69,164)}
assert incoming[164]==[[135,1,1,'R',164],[205,0,0,'R',164]]
assert incoming[69]==[[53,1,1,'R',69],[100,0,0,'R',69]]
for item in record['binding_failures']:
 p=item['path'];assert ('1'+p+'1').endswith('101') and item['state']==108 and item['allowed']==[13] and not item['tape_changed']
 n=t
 for b in p:n=n[int(b)]
 assert n==(('CD',6),('CC',2))
seen={0};queue=[0]
for q in queue:
 for b in (0,1):
  z=N[q,b][2]
  if z!=254 and z not in seen:seen.add(z);queue.append(z)
assert seen=={q for q,b in N}
held=rows(P/'held-candidate-review.json');assert held['status']=='HELD_TABLE_PREFIX_AND_LITERAL_ENTRY_PASS'and held['internal_prefixes']==4750 and held['leaf_entries']==4751
freeze=rows(P/'candidate-freeze.json')
for rel,digest in freeze['files'].items():assert sha(P/rel)==digest
out={'status':'PASS_INDEPENDENT_PROSPECTIVE_SOURCE_AND_LITERAL_REVIEW','scope':'Own source parsing/full ordinal CFG equality/literal table and marker premises. No supplied Python imports, allocator, machine runtime, blank replay or proof compiler invocation.','metrics':met,'source_sha256':sha(P/'sites-210.json'),'table_sha256':sha(P/'allocation210-run2/candidate.native.tm'),'guarded_successor_edges':6175,'halt_cases':1,'same_primitive_word_and_CFG_as_checked210':True,'complete_partial_selector_subtree_preserved':True,'partial_selector_new_span':[398,4572],'rows':430,'working_states':215,'removed_states':removed,'changed_retained_rows':changes,'graph_reachable_working_states':len(seen),'incoming_marker_rows':incoming,'eight_108_alias_suffixes_checked':True,'opening_finite_audit_attributed':{'path':str(P/'held-candidate-review.json'),'sha256':sha(P/'held-candidate-review.json'),'not_reexecuted':True},'frozen_candidate_packet_sha256':sha(P/'candidate-freeze.json'),'own_reader_sha256':sha(Path(__file__))}
(O/'inspection.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='changed_retained_rows'},indent=2))
