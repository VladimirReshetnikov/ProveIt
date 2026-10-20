"""Own metadata/enumeration audit, not a second semantic checker execution."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,itertools,json
ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 t={}
 for line in p.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,z=line.split();t[int(q),int(b)]=int(w),1 if d=='R'else -1,int(z)
 return t

def expected_groups(t):
 states=sorted({q for q,b in t});inc={q:[]for q in states}
 for(q,b),(w,d,z)in t.items():
  if z in inc:inc[z].append((q,d))
 groups={}
 for drop in states:
  if drop==0:continue
  for keep in states:
   if keep==drop:continue
   ds={d for q,d in inc[drop]if q!=keep and q!=drop}
   for shift in[-2,2]:
    if any(d+shift not in[-1,1]for d in ds):continue
    choices=[]
    for bit in[0,1]:
     c=set()
     for q in[keep,drop]:
      w,d,z=t[q,bit];target=keep if z==drop else z;c.add((w,d,target))
      if z==drop and -1<=d+shift<=1:c.add((w,d+shift,target))
     choices.append(c)
    groups[keep,drop,shift]=set(itertools.product(*choices))
 return groups

out=[]
for name in ['zero_terminal','zero_terminal-row157','retagged','retagged-row157','composed','composed-row157']:
 d=ROOT/('shifted-'+name);r=json.loads((d/'result.json').read_text());t=table(d/'old.tm');groups=expected_groups(t);count=0;seen=set();previous=None;observed=Counter()
 assert sha(d/'old.tm')==r['old_sha256']and sha(d/'search.py')==r['search_sha256']and sha(d/'check_shifted.py')==r['checker_sha256']
 assert r['status']=='COMPLETE_BOUNDED_FAMILY'and not r['partial_pair_shifts']and not r['survivors']
 with gzip.open(d/'rejections.jsonl.gz','rt')as f:
  for line in f:
   x=json.loads(line);count+=1;assert x['id']==count;key=x['keep'],x['drop'],x['shift'];actions=tuple(map(tuple,x['actions']))
   if key!=previous:
    if previous is not None:assert seen==groups[previous]
    previous=key;seen=set()
   assert actions in groups[key]and actions not in seen;seen.add(actions);observed[key]+=1
   q,b=x['failure']['row'];word=x['failure']['window'];assert q in(key[0],key[1])and b in(0,1)and 0<=word<32768 and(word>>7)&1==b
 assert seen==groups[previous]
 assert set(observed)==set(groups)and all(observed[k]==len(v)for k,v in groups.items())
 assert count==r['attempted']==r['filter_rejected']==sum(len(v)for v in groups.values())
 assert len(groups)==r['completed_pair_shifts']==r['eligible_pair_shifts_visited']
 out.append({'name':name,'status':r['status'],'candidates':count,'pair_shifts':len(groups),'seconds':r['seconds'],'old_sha256':r['old_sha256'],'result_sha256':sha(d/'result.json'),'rejections_sha256':sha(d/'rejections.jsonl.gz')})
stack=[]
for n in ['zero_terminal','retagged','composed']:
 p=ROOT/(n+'-row157')/'joint.json';r=json.loads(p.read_text());assert r['status']=='INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS'and r['negative_control']['status']=='REJECTED'
 stack.append({'variant':n,'record_sha256':sha(p),'nontrivial_contexts':r['nontrivial_contexts'],'invariant_contexts':r['inductive_window_contexts'],'max_old_new':[r['maximum_old_block'],r['maximum_new_block']]})
fail=json.loads((ROOT/'failure-transfer.json').read_text());assert len(fail['variants'])==6 and all(len(x['wrong_endpoints'])==4 and len(x['divergence'])==3 for x in fail['variants'])
summary={'status':'COMPLETE_ENUMERATION_AND_EVIDENCE_METADATA_PASS','shifted_searches':out,'total_candidates':sum(x['candidates']for x in out),'total_pair_shifts':sum(x['pair_shifts']for x in out),'total_search_seconds':sum(x['seconds']for x in out),'partial_pairs':0,'shifted_survivors':0,'row157_stacks':stack,'specific_failure_transfers':42,'failure_transfer_literal_steps':fail['literal_steps'],'failure_transfer_sha256':sha(ROOT/'failure-transfer.json'),'audit_source_sha256':sha(Path(__file__)),'scope':'Metadata and independent family enumeration only. No search replay; no shifted state reduction found. Candidate filter rejection remains incomplete; three positive row157 records are independent full-tape certificates, conditional on correctness of their source tables.'}
(ROOT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
