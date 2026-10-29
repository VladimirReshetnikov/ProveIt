from pathlib import Path
import json,hashlib,zipfile,subprocess
D=next(Path('Computability/DiophantineConsistency/reviews').glob('*kernel-range-projections-evidence'));b=json.loads((D/'BUNDLE.json').read_text());Z=D/b['archive'];h=lambda d:hashlib.sha256(d).hexdigest();assert h(Z.read_bytes())==b['archive_sha256']
with zipfile.ZipFile(Z) as z:
 assert z.testzip() is None
 names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(b['members'])
 for n in names:
  d=z.read(n);m=b['members'][n];assert h(d)==m['sha256'] and len(d)==m['bytes']
 print('archive SHA, CRC, member hashes/sizes verified',len(names));get=lambda n:z.read(n);rec=lambda n:json.loads(get('prototype/'+n));repo='Computability/DiophantineConsistency/'
 assert subprocess.check_output(['git','rev-parse',b['source_commit']+'^']).decode().strip()==b['source_parent']
 for group,name,folder in [('Lean','SplitKernelData59.lean','Lean/DiophantineConsistency'),('Lean','GapKernelData66.lean','Lean/DiophantineConsistency'),('tools','generate_split_kernels59.py','tools'),('tools','generate_gap_kernels66.py','tools')]:
  for ph,ref in [('baseline',b['source_parent']),('final',b['source_commit'])]:
   data=subprocess.check_output(['git','show',ref+':'+repo+folder+'/'+name]);assert data==get(f'commit/{ph}/{group}/{name}')==get(f'snapshots/{ph}/{folder}/{name}')
 for n in ['SplitKernels59','GapKernels66']:
  data=subprocess.check_output(['git','show',b['source_commit']+':'+repo+'Lean/DiophantineConsistency/'+n+'.lean']);assert data==get(f'snapshots/baseline/Lean/DiophantineConsistency/{n}.lean')==get(f'snapshots/final/Lean/DiophantineConsistency/{n}.lean')
 assert get('independent/kernel-range-independent-review.txt')==(D/'independent-review.txt').read_bytes();print('commit/parent Lean, generators, wrappers and review verified')
 for x in rec('generator-check-records.json'):
  assert x['status']==0 and x['before']==x['after'] and x['log_sha256']==h(get('prototype/'+Path(x['log']).name))
  for path,sha in x['before'].items():
   ph=x['phase']
   if '/Proofs/Computability/' in path:n='inputs/Computability/'+path.split('/Proofs/Computability/',1)[1]
   elif '/tools/' in path:n='snapshots/'+ph+'/tools/'+Path(path).name
   else:n='snapshots/'+ph+'/Lean/DiophantineConsistency/'+Path(path).name
   assert h(get(n))==sha,(path,n)
 print('four generator checks and all data/helper pins verified')
 for x in json.loads(get('independent/regeneration-records.json')):
  ph=x['phase'];kind=x['kind'];assert x['status']==0 and x['external_inputs_before']==x['external_inputs_after']
  for path,sha in x['external_inputs_before'].items():assert h(get('inputs/Computability/'+path.split('/Proofs/Computability/',1)[1]))==sha
  script='generate_split_kernels59.py' if kind=='split' else 'generate_gap_kernels66.py';assert x['script_sha256']==h(get(f'snapshots/{ph}/tools/{script}'))
  for name,sha in x['outputs'].items():assert sha==h(get(f'snapshots/{ph}/Lean/DiophantineConsistency/{name}'))
  assert x['log_sha256']==h(get(f'prototype/gen-{ph}-{kind}.log'))
 print('four independent regeneration receipts verified')
 prior={}
 for f in ['geometry-provider-records.json','wordbounds-provider-records.json']:
  for x in rec(f):
   if x.get('phase','final')=='final' and x['status']==0:
    n=x['module'];assert x['before']==x['after'];prior[n]=x
    ref='dcba8839c3^' if n=='SelectiveCoefficientBounds' else b['source_commit'];assert x['before']==h(subprocess.check_output(['git','show',ref+':'+repo+'Lean/DiophantineConsistency/'+n+'.lean']))
 rows={}
 for ph in ['baseline','final']:
  for x in rec('kernel-'+ph+'-records.json'):
   n=x['module'];assert x['status']==0 and x['before']==x['after']==h(get(f'snapshots/{ph}/Lean/DiophantineConsistency/{n}.lean')) and x['log_sha256']==h(get(f'prototype/kernel-{ph}-{n}.log')) and x['time'].encode()==get(f'prototype/kernel-{ph}-{n}.time')
   for d in x['direct_inputs']:
    assert d['before']==d['after'];m=d['module'].split('.')[-1]
    if m in prior:assert d['before']==prior[m]['object_sha256']
    elif (ph,m) in rows:assert d['before']==rows[ph,m]['object_sha256'] and d['resolved']==rows[ph,m]['object']
    else:assert d['module']=='Mathlib.Tactic.Linarith'
   rows[ph,n]=x
 assert len(rows)==8
 for n in ['SplitKernelData59','GapKernelData66','SplitKernels59','GapKernels66']:assert rows['baseline',n]['object_sha256']!=rows['final',n]['object_sha256']
 print('eight target/wrapper builds, direct providers and changed object hashes verified')
 for f,mods in [('coherent-probe-records.json',['SplitKernelData59','GapKernelData66']),('client-probe-records.json',['SplitKernelData59','GapKernelData66','SplitKernels59','GapKernels66'])]:
  rr=rec(f);assert len(rr)==10
  for x in rr:
   assert x['status']==0 and x['source_before']==x['source_after']==h(get('prototype/'+Path(x['source']).name)) and x['log_sha256']==h(get('prototype/'+Path(x['log']).name)) and x['objects_before']==x['objects_after']==[rows[x['phase'],n]['object_sha256'] for n in mods]
 for prefix,ns in [('probe',['names','coherent-interfaces','simp','instances','private']),('client-probe',['client-names','client-interfaces','client-simp','client-instances','client-private'])]:
  for n in ns:assert get(f'prototype/{prefix}-baseline-{n}.log')==get(f'prototype/{prefix}-final-{n}.log')
 print('twenty probes and all paired reports verified')
 assert sum(v.startswith('DECL ') for v in get('prototype/probe-baseline-names.log').decode().splitlines())==88
 assert sum(v.startswith('DECL ') for v in get('prototype/client-probe-baseline-client-names.log').decode().splitlines())==36
 def axiom_count(name):
  t=get('prototype/'+name).decode();return t.count('depends on axioms:')+t.count('does not depend on any axioms')
 assert axiom_count('probe-baseline-coherent-interfaces.log')==82 and axiom_count('client-probe-baseline-client-interfaces.log')==36
 assert sum(v.startswith('PRIVATE ') for v in get('prototype/probe-baseline-private.log').decode().splitlines())==6 and not get('prototype/client-probe-baseline-client-private.log')
 for n,num in [('simp',55118),('instances',23324)]:assert len(get('prototype/probe-baseline-'+n+'.log').splitlines())==num
 print('name, public/private report and registration counts verified')
 root='snapshots/prior-coefficient-receipts/';out=[]
 for ph,rf,cf in [('baseline','baseline-records.json','baseline-clients-records.json'),('final','final-records.json','final-clients2-records.json')]:
  x=next(q for q in json.loads(get(root+rf)) if q['module']=='SelectiveCoefficientBounds');y=next(q for q in json.loads(get(root+cf)) if q['module']=='PolynomialRangeBounds');assert x['status']==y['status']==0 and x['before']==x['after'] and y['direct_inputs'][0]['before']==y['direct_inputs'][0]['after']==x['object_sha256'] and y['direct_inputs'][0]['resolved']==x['object'];out.append(y['object_sha256'])
 assert out[0]==out[1]==prior['PolynomialRangeBounds']['object_sha256'];old=prior['SelectiveCoefficientBounds'];assert any(d['module'].endswith('.SelectiveCoefficientBounds') and d['before']==old['object_sha256'] for d in prior['PolynomialRangeBounds']['direct_inputs']);assert any(d['module'].endswith('.PolynomialRangeBounds') and d['before']==out[0] for d in prior['SplitWordBounds']['direct_inputs']);assert old['object_sha256']=='1f2bffef4cc603725a857ae379e246498e36d7d85ad5645c36fbc14adab1c1a8';assert old['before']!=h(subprocess.check_output(['git','show',b['source_commit']+':'+repo+'Lean/DiophantineConsistency/SelectiveCoefficientBounds.lean']));print('older SelectiveCoefficientBounds boundary and paired PolynomialRangeBounds hash verified')
 print('compiled objects excluded; cached transitive closure not rebuilt')
