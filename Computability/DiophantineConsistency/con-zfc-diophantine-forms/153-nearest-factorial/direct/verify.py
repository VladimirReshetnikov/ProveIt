#!/usr/bin/env python3
"""Offline independent exact checks of the nearest-factorial direct quartics."""
from pathlib import Path
import argparse,copy,json,os,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent

def run(cmd,success=True):
 p=subprocess.run(cmd,capture_output=True,text=True,cwd=ROOT)
 if success and p.returncode:raise RuntimeError(p.stdout+p.stderr)
 if not success and p.returncode==0:raise RuntimeError('Corruption was incorrectly accepted')
 return json.loads(p.stdout) if success else True

def read(p):return json.loads(p.read_text())
def write(p,x):p.write_text(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n')
def verify(mutations=True,rebuild=False):
 flags=['-B']+(['-O'] if sys.flags.optimize else [])
 py=[sys.executable,*flags]
 receipt={}
 receipt['base246']=run(py+[str(ROOT/'code/check_base.py'),'--source-dir',str(ROOT/'data'),'--endpoint-dir',str(ROOT/'data')])
 receipt['refinements']=run(py+[str(ROOT/'code/check_refine.py'),str(ROOT/'equations/P242'),str(ROOT/'equations/P243')])
 receipt['refinements']={Path(k).name:v for k,v in receipt['refinements'].items()}
 base=read(ROOT/'data/equation.json')
 for name in ['P242','P243']:
  if read(ROOT/'equations'/name/'source.json')!=base:raise ValueError('Refinement source is not the checked base246')
 receipt['refinement_source_binding']=True
 receipt['mutations_rejected']=[]
 if mutations:
  for mode in ['ceiling_ratio','ceiling_sign','shared_norm','front_guard','base_projection','refinement_projection','row_operation','coefficient','embedded_metric','coordinate_metadata']:
   with tempfile.TemporaryDirectory(prefix='conzfc-control-') as td:
    d=Path(td)/'work'
    if mode in ['ceiling_ratio','ceiling_sign','shared_norm','front_guard','base_projection']:
     shutil.copytree(ROOT/'data',d)
     file='source.json' if mode in ['ceiling_ratio','ceiling_sign'] else 'projection_certificate.json' if mode=='base_projection' else 'guarded.json'
     x=read(d/file)
     if mode=='ceiling_ratio':
      r=next(r for r in x['residuals'] if r['label']=='remainder_budget.ceiling_ratio');r['terms'][0][0]+=1
     elif mode=='ceiling_sign':
      r=next(r for r in x['residuals'] if r['label']=='remainder_budget.ceiling_scaled');r['terms'][0][0]*=-1
     elif mode=='shared_norm':x['residuals'][-1]['terms'][0][0]+=1
     elif mode=='front_guard':x['residuals'].append(copy.deepcopy(x['residuals'][-1]))
     else:x['steps'][0]['restoration'][0][0]+=1
     write(d/file,x)
     run(py+[str(ROOT/'code/check_base.py'),'--source-dir',str(d),'--endpoint-dir',str(d)],False)
    else:
     shutil.copytree(ROOT/'equations/P242',d)
     file={'refinement_projection':'projection_certificate.json','row_operation':'certificate.json','coefficient':'expanded_polynomial.json','embedded_metric':'equation.json','coordinate_metadata':'equation.json'}[mode]
     x=read(d/file)
     if mode=='refinement_projection':x['steps'][0]['restoration'][0][0]+=1
     elif mode=='row_operation':x['final_operations'][0][2]+=1
     elif mode=='coefficient':x['terms'][0][0]+=1
     elif mode=='embedded_metric':x['metrics']['monomials']+=1
     else:x['variables'][0]['source_name']='incorrect'
     write(d/file,x);run(py+[str(ROOT/'code/check_refine.py'),str(d)],False)
   receipt['mutations_rejected'].append(mode)
 if rebuild:
  with tempfile.TemporaryDirectory(prefix='conzfc-base-rebuild-') as td:
   d=Path(td)/'data';run(py+[str(ROOT/'code/build.py'),str(d),'--scale-digits'])
   expected=sorted(p.name for p in (ROOT/'data').glob('*.json'))
   if expected!=sorted(p.name for p in d.glob('*.json')):raise ValueError('Rebuild inventory')
   for name in expected:
    if (ROOT/'data'/name).read_bytes()!=(d/name).read_bytes():raise ValueError('Base rebuild differs: '+name)
   receipt['base_rebuilt_identically']=expected
  receipt['refined_rebuilt_identically']={}
  for name in ['P242','P243']:
   with tempfile.TemporaryDirectory(prefix='conzfc-refined-rebuild-') as td:
    d=Path(td);run(py+[str(ROOT/'code/replay_refined.py'),str(ROOT/'equations'/name),str(d)])
    files=['equation.json','expanded_polynomial.json','METRICS.json']
    for f in files:
     if (ROOT/'equations'/name/f).read_bytes()!=(d/f).read_bytes():raise ValueError('Refined rebuild differs: '+name+'/'+f)
    receipt['refined_rebuilt_identically'][name]=files
 receipt['python_optimization']=sys.flags.optimize
 receipt['scope']='Exact finite construction, transformations and coefficients. No consistency decision or end-to-end proof-assistant claim.'
 return receipt
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--skip-mutations',action='store_true');p.add_argument('--rebuild',action='store_true');p.add_argument('--receipt',type=Path);a=p.parse_args();r=verify(not a.skip_mutations,a.rebuild)
 if a.receipt:a.receipt.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps(r,indent=2))
