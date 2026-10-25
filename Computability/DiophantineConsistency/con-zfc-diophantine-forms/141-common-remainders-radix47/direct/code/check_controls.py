#!/usr/bin/env python3
"""Corruption controls for the independent normalized-remainder audit."""
import argparse,json,pathlib,tempfile,shutil,subprocess,sys
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--source-dir',type=pathlib.Path,required=True)
p.add_argument('--endpoint-dir',type=pathlib.Path,required=True)
p.add_argument('--checker',type=pathlib.Path,default=pathlib.Path(__file__).with_name('check.py'))
a=p.parse_args()
flags=[] if __debug__ else ['-O']
controls=[('source','source.json','ratio_coefficient'),('source','source.json','digit_coefficient'),('source','guarded.json','budget_coefficient'),('source','projection_certificate.json','restoration'),('endpoint','translation_certificate.json','translation'),('endpoint','expanded_polynomial.json','quartic_coefficient'),('source','factorization_certificate.json','factor_root')]
results=[]
for which,file,kind in controls:
 with tempfile.TemporaryDirectory(prefix='normalized-audit-') as tmp:
  root=pathlib.Path(tmp);s=root/'source';e=root/'endpoint';shutil.copytree(a.source_dir,s);shutil.copytree(a.endpoint_dir,e)
  target=(s if which=='source' else e)/file;d=json.loads(target.read_text())
  if kind=='factor_root':next(iter(d['square_roots'].values()))[0][0]+=1
  elif kind=='ratio_coefficient':
   r=next(r for r in d['residuals'] if r['label']=='remainder_budget.ratio0');r['terms'][0][0]+=1
  elif kind=='digit_coefficient':
   r=next(r for r in d['residuals'] if r['label']=='choose0.digit');r['terms'][0][0]+=1
  elif kind=='budget_coefficient':d['residuals'][-1]['terms'][0][0]+=1
  elif kind=='restoration':d['steps'][0]['restoration'][0][0]+=1
  elif kind=='translation':d['shifts'][0][1]+=1
  elif kind=='quartic_coefficient':d['terms'][0][0]+=1
  target.write_text(json.dumps(d))
  r=subprocess.run([sys.executable,*flags,str(a.checker),'--source-dir',str(s),'--endpoint-dir',str(e)],capture_output=True,text=True)
  if r.returncode==0:raise ValueError('Corruption accepted: '+kind)
  if 'Independent verification failed' not in r.stderr and 'factor square root mismatch' not in r.stderr:raise ValueError('Unexpected checker failure: '+r.stderr)
  results.append({'mutation':kind,'rejected':True})
print(json.dumps({'status':'PASS','mode':'normal' if __debug__ else 'optimized','negative_controls':results},indent=2))
