import json,hashlib,zipfile,subprocess,re
from pathlib import Path
D=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-binom-odd-sharing-evidence');b=json.loads((D/'BUNDLE.json').read_text());Z=D/b['archive'];h=lambda x:hashlib.sha256(x).hexdigest();assert h(Z.read_bytes())==b['archive_sha256']
with zipfile.ZipFile(Z) as z:
 assert z.testzip() is None
 names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(b['members'])
 for n in names:
  x=z.read(n);m=b['members'][n];assert len(x)==m['bytes'] and h(x)==m['sha256']
 print('ZIP SHA, CRC, membership, sizes and hashes verified:',len(names))
 get=lambda n:z.read(n)
 path='Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticBinomLegendre.lean'
 for phase,rev in [('baseline',b['source_parent']),('final',b['source_commit'])]:
  g=subprocess.check_output(['git','show',rev+':'+path]);assert g==get(f'commit/{phase}/ArithmeticBinomLegendre.lean')==get(f'prototype/{phase}-commit.lean')==get(f'snapshots/{phase}/DiophantineConsistency/ArithmeticBinomLegendre.lean')==get(f'snapshots/{phase}-repeat/DiophantineConsistency/ArithmeticBinomLegendre.lean')
 assert subprocess.check_output(['git','rev-parse',b['source_commit']+'^']).decode().strip()==b['source_parent']
 assert get('independent/binom-odd-independent-review.txt')==(D/'independent-review.txt').read_bytes()
 print('source snapshots, parent and independent review verified')
 rows={}
 for phase in ['baseline','final','baseline-repeat','final-repeat']:
  rows[phase]=json.loads(get(f'prototype/{phase}-records.json'))
  for r in rows[phase]:
   assert r['status']==0 and r['before']==r['after']
   snap=f'snapshots/{phase}/DiophantineConsistency/{r["module"]}.lean'; assert h(get(snap))==r['before']
   if r['module']!='ArithmeticBinomLegendre':
    p='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+r['module']+'.lean';assert get(snap)==subprocess.check_output(['git','show',b['source_commit']+':'+p])
   assert h(get(f'prototype/{phase}-{r["module"]}.log'))==r['log_sha256']
   assert get(f'prototype/{phase}-{r["module"]}.time').decode()==r['time']
   for d in r['direct_inputs']:
    assert d['before']==d['after']
    earlier=next((x for x in rows[phase] if x['module']==d['module'].split('.')[-1]),None)
    if earlier: assert earlier['object_sha256']==d['before'] and earlier['object']==d['resolved']
  print(phase,'successful records:',len(rows[phase]))
 for a,c in zip(rows['baseline'][1:],rows['final'][1:]):assert a['module']==c['module'] and a['object_sha256']==c['object_sha256']
 for phase in ['baseline','final']:
  for name in ['names','interfaces','simp','instances']:
   p=json.loads(get(f'prototype/probe-{name}-{phase}.json'));assert p['status']==0 and p['source_before']==p['source_after']==h(get(f'prototype/{name}.lean')) and p['object_before']==p['object_after']==rows[phase][0]['object_sha256'] and p['log_sha256']==h(get(f'prototype/{phase}-{name}.log'))
 for n in ['simp','instances']:assert get(f'prototype/baseline-{n}.log')==get(f'prototype/final-{n}.log')
 def blocks(phase):
  s=get(f'prototype/{phase}-interfaces.log').decode();return {v.split(' TYPE ',1)[0]:v for v in re.split(r'(?m)^DECL ',s) if v.strip()}
 a,c=blocks('baseline'),blocks('final');assert len(a)==11 and len(c)==12 and all(c[k]==v for k,v in a.items());print('declarations and registration probes match; extra',*(c.keys()-a.keys()))
 priors=[]
 for p in ['provider/outer-seed-bound-sharing/prereq2-records.json','provider/pell-construction-refresh/resumed-records.json']:priors.extend(json.loads(get(p)))
 for r in rows['baseline']:
  for d in r['direct_inputs']:
   if d['module'].split('.')[-1] in [x['module'] for x in rows['baseline']]:continue
   src=Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency')/(d['module'].split('.')[-1]+'.lean');sh=h(src.read_bytes())
   assert any(q.get('status')==0 and q.get('module') in [d['module'],d['module'].split('.')[-1]] and q.get('source_sha256')==sh and q.get('object_sha256')==d['before'] for q in priors)
   print('direct provider prior receipt',d['module'])
 print('All archive checks pass; object bytes and cached transitive closure excluded.')
