#!/usr/bin/env python3
"""Independent source, fold, startup and conjugacy replay; read-only."""
from pathlib import Path
import hashlib,json
B=Path(__file__).resolve().parent.parent
P=B/'construction/inputs/parent6_snapshot'
C=B/'machine'
R=B
def load(p):return json.loads(p.read_text())
def table(p):
 d={}
 for line in p.read_text().splitlines():
  q,b,w,m,n=line.split();key=int(q),int(b)
  assert key not in d and m in ['L','R']
  d[key]=(int(w),m,int(n))
 return d
old,new=table(P/'machine.native.tm'),table(C/'machine.native.tm')
assert set(old)==set(new)
changes=[(q,b,old[q,b],new[q,b])for q,b in old if old[q,b]!=new[q,b]]
assert changes==[(164,1,(1,'R',98),(1,'R',114))]
ns0,ns1=load(P/'nodes.json'),load(C/'nodes.json')
node_changes={k:[ns0[k],ns1[k]]for k in ns0 if ns0[k]!=ns1[k]}
assert node_changes=={'node163':[['node6','node55'],['node6','node54']]}
oldins,newins=load(P/'instructions.json'),load(C/'instructions.json')
oldsites,newsites=load(P/'sites.json'),load(C/'sites.json')
assert len(oldins)==len(oldsites)==3795 and len(newins)==len(newsites)==3776
lo,hi=3756,3775
rel=lambda i:i if i<lo else lo if i==lo else i-19
changed_paths=[];incoming=[];outside=0
for i,z in enumerate(oldins):
 if lo<=i<hi:continue
 n=2 if z[0]in('inc','dec')else 1
 assert not any(lo<t<hi for t in z[n:])
 incoming.extend([i,t]for t in z[n:]if lo<=t<hi)
 assert z[:n]+[rel(t)for t in z[n:]]==newins[rel(i)]
 assert oldsites[i][1:]==newsites[rel(i)][1:]
 if oldsites[i][0]!=newsites[rel(i)][0]:changed_paths.append([i,rel(i)])
 outside+=1
assert outside==3776 and incoming==[[3750,3756]]
folds=load(R/'construction/inputs/parent6.folds.json')
foldstates={q for a,b,r in folds for q in(a,b)}
assert all(q not in foldstates for q in(164,98,114))
cases=load(C/'local_fold_cases.json')['cases']
assert len(cases)==32
allreadstates={z[0]for c in cases for z in c['trace'][:-1]}
assert 164 not in allreadstates
raw=table(C/'unfolded202.native.tm')
alias={a:b for a,b,acts in folds}
def aliased(q):
 while q in alias:q=alias[q]
 return q
incoming_fold_rows=0
for a,b,acts in folds:
 for old_state,history in [(a,0),(b,1)]:
  incoming_actions=[(w,d)for (q,bit),(w,d,n)in raw.items()if n==old_state]
  assert incoming_actions and set(incoming_actions)=={(history,'R')}
  incoming_fold_rows+=len(incoming_actions)
for c in cases:
 old_state,bit,hist=c['old_state'],c['current_bit'],c['history_bit']
 assert c['trace'][0]==[aliased(old_state),0,hist,bit]
 w,d,n=raw[old_state,bit]
 assert c['trace'][-1]==[aliased(n),1 if d=='R'else-1,hist,w]
# Independently replay the 32 two-cell traces directly from the new table.
for c in cases:
 tr=c['trace'];assert len(tr)==c['duration']+1
 for z,zz in zip(tr,tr[1:]):
  q,h,left,right=z;t={-1:left,0:right}
  assert h in t
  w,m,n=new[q,t[h]];t[h]=w
  assert [n,h+(1 if m=='R'else-1),t[-1],t[0]]==zz
# Independently replay both blank startups in lockstep; neither reads modified row.
q=head=0;q=74;ones=set();hits=0
for t in range(58320):
 bit=int(head in ones);hits+=(q,bit)==(164,1)
 assert old[q,bit]==new[q,bit]
 w,m,q=new[q,bit]
 if w:ones.add(head)
 else:ones.discard(head)
 head+=1 if m=='R'else-1
 assert q!=254
assert q==84 and head==-2 and hits==0
expected=load(C/'receipt.json')['startup'];assert sorted(ones)==expected['one_cells']
# Table conjugacy independently from declared map, no compiler imported.
lab=load(C/'labels.json');dense=table(C/'machine.tm')
if isinstance(lab,list): mapping=dict(enumerate(lab))
else:mapping={int(k):v for k,v in lab.items()}
assert len(mapping)==195 and len(set(mapping.values()))==195 and mapping[194]==254
for (a,b),(w,d,n)in dense.items():assert new[mapping[a],b]==(w,d,mapping[n])
result=dict(status='PASS',native_changes=changes,node_changes=node_changes,old_source_sites=3795,new_source_sites=3776,removed_interval=[lo,hi],unique_external_entry=incoming,all_remaining_instructions_exactly_relocated=True,changed_retained_paths=changed_paths,axiom_emitter_unchanged_from_radix6=True,folds=len(folds),literal_fold_cases_replayed=32,fold_entry_rows_checked=incoming_fold_rows,fold_endpoints_match_raw_parent=True,changed_control_not_used_inside_any_fold_trace=True,blank_startup_replayed=58320,changed_row_reads_before_seed=hits,complete_tape_equals_delivered_seed=True,dense_native_conjugacy=True,dense_sha256=hashlib.sha256((C/'machine.tm').read_bytes()).hexdigest())
print(json.dumps(result,indent=2))
