"""Compare the completed independent endpoint reconstructions with the frozen producer records."""
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parent;SOURCE=HERE.parent/'profile_370';rows=[]
for mode,name in [('zero0','zero_overlap_zero'),('h0','zero_overlap_h'),('zero','zero'),('g','g'),('h','h')]:
 local=HERE/f'check_{mode}.json';a=json.loads(local.read_text());b=json.loads((SOURCE/f'certificate_{name}.json').read_text())
 for key in ('coefficient_sha256','positive_coefficients','scalar_sha256'):
  if a[key]!=b[key]:raise RuntimeError(('comparison',mode,key,a[key],b[key]))
 if not a['all_pass'] or b['status']!='pass':raise RuntimeError(('sign check',mode))
 a['matched_primary_hash']=True;local.write_text(json.dumps(a,indent=2)+'\n');rows.append({'mode':mode,'positive_coefficients':a['positive_coefficients'],'coefficient_sha256':a['coefficient_sha256']})
m=json.loads((HERE/'check_scalar.json').read_text())
if not m['all_pass'] or m['quadratic_coefficient_identities']!=10:raise RuntimeError('matrix identity receipt')
files=['check_regions.py','check_scalar.py','finalize.py','check_scalar.json']+[f'check_{mode}.json' for mode in ('zero0','h0','zero','g','h')]
out={'all_pass':True,'regions':5,'positive_coefficients':sum(x['positive_coefficients'] for x in rows),'fresh_seven_class_quadratic_identities':10,'records':rows,'files':{n:hashlib.sha256((HERE/n).read_bytes()).hexdigest() for n in files}}
(HERE/'independent_manifest.json').write_text(json.dumps(out,indent=2)+'\n');print('ALL FIVE HASHES MATCH',out['positive_coefficients'])
