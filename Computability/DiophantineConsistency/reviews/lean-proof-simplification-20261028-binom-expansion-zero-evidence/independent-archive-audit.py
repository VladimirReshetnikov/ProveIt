from pathlib import Path
import json,hashlib,zipfile,subprocess,re
D=next(Path('Computability/DiophantineConsistency/reviews').glob('*binom-expansion-zero-evidence'));b=json.loads((D/'BUNDLE.json').read_text());Z=D/b['archive'];h=lambda x:hashlib.sha256(x).hexdigest();assert h(Z.read_bytes())==b['archive_sha256']
with zipfile.ZipFile(Z) as z:
 assert z.testzip() is None
 names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(b['members'])
 for n in names:
  x=z.read(n);m=b['members'][n];assert h(x)==m['sha256'] and len(x)==m['bytes']
 print('ZIP SHA/CRC and all member hashes/sizes verified:',len(names));get=lambda n:z.read(n);rec=lambda n:json.loads(get('prototype/'+n));repo='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
 assert subprocess.check_output(['git','rev-parse',b['source_commit']+'^']).decode().strip()==b['source_parent']
 n='ArithmeticBinomExpansion'
 for ph,ref in [('baseline',b['source_parent']),('final',b['source_commit'])]:assert subprocess.check_output(['git','show',ref+':'+repo+n+'.lean'])==get(f'commit/{ph}.lean')==get(f'snapshots/{ph}/DiophantineConsistency/{n}.lean')
 for ph in ['baseline','final']:assert get(f'snapshots/{ph}/DiophantineConsistency/ArithmeticHalfBinomial.lean')==subprocess.check_output(['git','show',b['source_commit']+':'+repo+'ArithmeticHalfBinomial.lean'])
 assert get('independent/binom-expansion-independent-review.txt')==(D/'independent-review.txt').read_bytes();print('commit/parent target and client snapshots, review verified')
 prior=[]
 for f in ['provider/outer-seed-bound-sharing/prereq2-records.json','provider/pell-construction-refresh/resumed-records.json','provider/binom-odd-sharing/final-records.json']:
  for x in json.loads(get(f)):
   if x.get('status')==0:prior.append((x.get('module','').split('.')[-1],x.get('source_sha256',x.get('before')),x.get('object_sha256')))
 rows={};providers=set()
 for ph in ['baseline','final']:
  for x in rec(ph+'-records.json'):
   n=x['module'];assert x['status']==0 and x['before']==x['after']==h(get(f'snapshots/{ph}/DiophantineConsistency/{n}.lean')) and x['log_sha256']==h(get(f'prototype/{ph}-{n}.log')) and x['time'].encode()==get(f'prototype/{ph}-{n}.time')
   for d in x['direct_inputs']:
    assert d['before']==d['after'];m=d['module'].split('.')[-1]
    if (ph,m) in rows:assert d['before']==rows[ph,m]['object_sha256'] and d['resolved']==rows[ph,m]['object']
    else:source=h(subprocess.check_output(['git','show',b['source_commit']+':'+repo+m+'.lean']));assert (m,source,d['before']) in prior;providers.add(m)
   rows[ph,n]=x
  for n in ['names','interfaces','simp','instances']:
   x=rec('probe-'+n+'-'+ph+'.json');assert x['status']==0 and x['source_before']==x['source_after']==h(get(f'prototype/{n}.lean')) and x['object_before']==x['object_after']==rows[ph,'ArithmeticBinomExpansion']['object_sha256'] and x['log_sha256']==h(get(f'prototype/{ph}-{n}.log'))
 assert len(rows)==4 and len(providers)==4 and rows['baseline','ArithmeticHalfBinomial']['object_sha256']==rows['final','ArithmeticHalfBinomial']['object_sha256'];print('four builds, eight probes, four provider pairs and identical client verified')
 def decls(ph):return {v.split(' TYPE ',1)[0]:v for v in re.split(r'(?m)^DECL ',get(f'prototype/{ph}-interfaces.log').decode()) if v.strip()}
 a,c=decls('baseline'),decls('final');assert len(a)==40 and len(c)==41 and all(a[k]==c[k] for k in a);print('unchanged prior declarations; added',list(c.keys()-a.keys()))
 for n,num in [('simp',29034),('instances',13227)]:
  x=get('prototype/baseline-'+n+'.log');assert x==get('prototype/final-'+n+'.log') and len(x.splitlines())==num
 print('matching simp and instance reports verified')
 f=json.loads(get('snapshots/failed-simp/final-records.json'))[0];assert f['status']!=0 and f['before']==f['after']==h(get('snapshots/failed-simp/source.lean')) and f['log_sha256']==h(get('snapshots/failed-simp/final-ArithmeticBinomExpansion.log')) and f['time'].encode()==get('snapshots/failed-simp/final-ArithmeticBinomExpansion.time');assert get('snapshots/failed-simp/final-ArithmeticBinomExpansion.log').count(b'error: unsolved goals')==2
 pow=next(x for x in json.loads(get('provider/outer-seed-bound-sharing/prereq-records.json')) if x['module']=='DiophantineConsistency.ArithmeticPow');summary=next(x for x in json.loads(get('provider/outer-seed-bound-sharing/prereq2-records.json')) if x['module']=='DiophantineConsistency.ArithmeticPow');assert pow['status']==0 and pow['source_sha256']==pow['source_after']==summary['source_sha256'] and pow['object_sha256']==summary['object_sha256'];print('failed attempt and fuller ArithmeticPow receipt verified')
 print('compiled objects excluded; object identity claims checked through recorded hashes')
