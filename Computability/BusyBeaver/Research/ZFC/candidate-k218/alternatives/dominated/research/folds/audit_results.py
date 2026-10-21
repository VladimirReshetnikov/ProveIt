#!/usr/bin/env python3
"""Own metadata audit of completed finite searches; does not run any candidate."""
from pathlib import Path
import json,gzip,hashlib,itertools
R=Path(__file__).resolve().parent
out=[]
for name in ['run1']:
 p=R/name/'result.json'
 if not p.exists():continue
 j=json.loads(p.read_text());assert j['status']=='COMPLETE_BOUNDED_SEARCH'
 seed=next(Path(x)for x in j['inputs']if x.endswith('.tm'));T={}
 for line in seed.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),-1 if d=='L'else 1,int(z))
 Q=sorted({q for q,b in T});hist={0:0,1:0,2:0};expected=0;inherited=0
 for keep,drop in itertools.permutations(Q,2):
  phi=lambda q:keep if q==drop else q
  acts=[{(T[q,b][0],T[q,b][1],phi(T[q,b][2]))for q in(keep,drop)}for b in(0,1)]
  common=sum(len(a)==1 for a in acts);hist[common]+=1
  inherited+=len(acts[0])*len(acts[1]);expected+=4*len(Q)if common==1 else len(acts[0])*len(acts[1])
 assert expected==j['stats']['attempted']==j['stats']['filter_rejected'];assert inherited==j['stats']['inherited']
 assert j['stats']['completed_pairs']==j['stats']['started_pairs']==len(Q)*(len(Q)-1)
 stream=R/name/'rejections.jsonl.gz';assert hashlib.sha256(stream.read_bytes()).hexdigest()==j['rejections_sha256']
 count=0;pair=None;pair_seen=set();pairs_seen=0;family_count={};first_states=set()
 with gzip.open(stream,'rt')as f:
  for line in f:
   r=json.loads(line);count+=1;assert r['id']==count and r['stage']=='bounded_filter';assert r['keep']in Q and r['drop']in Q and r['keep']!=r['drop'];assert r['start']==(r['keep']if r['drop']==0 else 0)
   assert r['witness']['radius']==7 and r['witness']['fuel']==97
   pk=(r['keep'],r['drop'])
   if pk!=pair:
    if pair is not None:pairs_seen+=1
    pair=pk;pair_seen=set()
   rowkey=tuple(tuple(x)for x in r['rows']);assert rowkey not in pair_seen;pair_seen.add(rowkey)
   phi=lambda q:r['keep']if q==r['drop']else q
   actions=[{(T[q,b][0],T[q,b][1],phi(T[q,b][2]))for q in pk}for b in(0,1)]
   if r['family']=='inherited':assert all(rowkey[b]in actions[b]for b in(0,1))
   else:
    common=[b for b in(0,1)if len(actions[b])==1];assert len(common)==1;fixed=common[0];other=1-fixed;assert rowkey[fixed]in actions[fixed] and rowkey[other]not in actions[other];w,d,z=rowkey[other];assert w in(0,1)and d in(-1,1)and z in(set(Q)-{r['drop']}|{254})
   family_count[r['family']]=family_count.get(r['family'],0)+1
   if 0 in pk:first_states.add(pk)
 if pair is not None:pairs_seen+=1
 assert count==expected and pairs_seen==len(Q)*(len(Q)-1)and len(first_states)==2*(len(Q)-1)
 assert family_count=={k:j['stats'][k]for k in ['inherited','one_common_action']}
 out.append({'run':name,'status':'PASS','ordered_pairs':pairs_seen,'candidate_specs':count,'initial_state_pairs':len(first_states),'common_branch_histogram':hist,'family_counts':family_count,'result_sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(R/'metadata-audit.json').write_text(json.dumps({'status':'PASS','runs':out,'scope':'Independent enumeration counts and full compressed stream membership/unique-per-pair checks; not a rerun or semantic interpretation of failed joins.'},indent=2)+'\n')
print(json.dumps(out,indent=2))
