#!/usr/bin/env python3
"""Independent finite counterexample to the shortened-return primitive contract."""
from pathlib import Path
import argparse,json,hashlib
from collections import Counter
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--baseline-table',type=Path,required=True);p.add_argument('--baseline-source',type=Path,required=True)
p.add_argument('--failed-table',type=Path,required=True);p.add_argument('--witness',type=Path,required=True)
p.add_argument('--summary',type=Path,required=True);args=p.parse_args()

def table(path):
 t={}
 for line in path.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();key=int(q),int(b);assert key not in t
  t[key]=int(w),1 if d=='R'else-1,int(z)
 return t

def clean(q,h,ones):
 if q!=84 or h-1 not in ones or any(x<h-1 for x in ones):return False
 right=sorted(x for x in ones if x>=h+52)
 if not right or right[0]<h+64:return False
 p=right[0]+1;last=max(ones);count=0
 while p<last:
  if p in ones or p+1 not in ones:return False
  count+=1;p+=1
  while p in ones:p+=1
 return p==last+1 and count>=10

def replay(t,initial,trace):
 q=84;h=0;ones=set(initial)
 for i,row in enumerate(trace):
  assert i==0 or not clean(q,h,ones)
  b=int(h in ones);w,d,z=t[q,b];assert[q,h,b,w,d,z]==row
  if w:ones.add(h)
  else:ones.discard(h)
  q=z;h+=d
 assert clean(q,h,ones)
 return {'state':q,'head':h,'one_cells':sorted(ones)}

r=json.loads(args.witness.read_text())
site=json.loads(args.baseline_source.read_text())[26]
assert site==r['site']==['1101001001000000','CD',1]
assert r['logical_registers']==[0]*9 and r['spares']==[0]and r['gap']==0
# All ten physical values arezero: ten blocks01 following header64.
initial={-1,64}|{i for i,b in enumerate(site[0])if b=='1'}|set(range(66,85,2))
assert sorted(initial)==r['initial_one_cells']
# Zero decrement escapes the finalzero ancestor and increments the remaining code.
stripped=site[0][:-1];expected_pc=format(int(stripped,2)+1,f'0{len(stripped)}b')
assert expected_pc=='110100100100001'
expected={-1,64}|{i for i,b in enumerate(expected_pc)if b=='1'}|set(range(66,85,2))
assert r['expected']=={'state':84,'head':0,'one_cells':sorted(expected)}
old=args.baseline_table;new=args.failed_table
assert hashlib.sha256(old.read_bytes()).hexdigest()==r['baseline_sha256']
assert hashlib.sha256(new.read_bytes()).hexdigest()==r['candidate_sha256']
T=table(old);N=table(new)
assert len(T)==430 and len(N)==428
assert N=={(q,b):(w,d,75 if z==50 else z)for(q,b),(w,d,z)in T.items()if q!=50}
a=replay(T,initial,r['baseline']['trace']);b=replay(N,initial,r['shortened_return']['trace'])
assert a==r['expected']
assert len(r['baseline']['trace'])==588 and len(r['shortened_return']['trace'])==662
assert set(b['one_cells'])^expected=={12,14}and b['state']==84 and b['head']==0
summary=json.loads(args.summary.read_text());source=json.loads(args.baseline_source.read_text())
assert summary['status']=='NOT_PROVED' and summary['expected_cases']==6176 and summary['proved_cases']==6104
assert summary['sites_sha256']==hashlib.sha256(args.baseline_source.read_bytes()).hexdigest()
assert summary['table_sha256']==hashlib.sha256(new.read_bytes()).hexdigest()
failures=summary['failures'];assert len(failures)==72
assert len({(f['site_index'],f['positive'])for f in failures})==72
sites={f['site_index']:f['site']for f in failures}
assert len(sites)==37 and all(source[i]==site and site[0].endswith('000000')for i,site in sites.items())
counts=Counter(op+str(arg)for path,op,arg in sites.values())
assert counts==Counter({'CD1':22,'CD2':11,'CD8':2,'CI1':2})
print(json.dumps({'status':'CONCRETE_PRIMITIVE_COUNTEREXAMPLE_AND_INHERITED_CENSUS_PASS',
 'baseline_steps':588,'candidate_steps':662,'expected_one_cell':14,'actual_one_cell':12,
 'inherited_proved_cases':6104,'inherited_unproved_cases':72,'unproved_source_occurrences':37,
 'occurrence_counts':dict(counts),
 'scope':'One valid arbitrary-frame semantic counterexample. Other71 are recorded failures to prove. No conclusion about blank-run equiconsistency.'},indent=2))
