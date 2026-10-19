#!/usr/bin/env python3
"""Offline exact K225 proof replay. --full freshly proves all6656 runtime cases.
The default audits the stored universal runtime certificate and reconstructs
source, table, all-tape fold, canonicalization, and complete blank startup.
--full-baseline additionally rederives the inherited K226 runtime proof.
No mode claims a new proof-assistant kernel check.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time,os
ROOT=Path(__file__).resolve().parent

def require(ok,message):
 if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def audit_runtime(report_path,table,source):
 r=json.loads(report_path.read_text());casespath=report_path.with_name(r['cases_file']);cases=json.loads(casespath.read_text())
 require(r['status']=='UNIVERSAL_MATHEMATICAL_PASS','Runtime not complete')
 require(r['table_sha256']==sha(table) and r['source_sha256']==sha(source),'Runtime input pins')
 require(r['engine_sha256']==sha(ROOT/'baseline226/vendor/proveit/symbolic_runtime.py') and r['helper_sha256']==sha(ROOT/'baseline226/vendor/proveit/independent_runtime.py'),'Runtime engine pins')
 require(r['cases_sha256']==sha(casespath),'Runtime cases pin')
 require(r['cases']==r['expected_cases']==len(cases)==6656,'Runtime cases census')
 require(r['states']==225 and r['rows']==450 and len(r['used_rows'])==450 and r['all_rows_used'],'Runtime state/row coverage')
 sites=json.loads(source.read_text());expected={(i,p)for i,(_,op,a)in enumerate(sites)for p in ((False,True)if op=='CD'else(False,))}
 require({(x['site_index'],x['positive'])for x in cases}==expected and len(expected)==len(cases),'Missing/duplicate instruction cases')
 require(sum(x['symbolic_steps']for x in cases)==r['symbolic_steps'],'Runtime rule sum')
 for x in cases:
  d=x['duration'];require(len(d)==13 and all(type(v)is int and v>=0 for v in d)and d[0]>0,'Positive unbounded duration')
 return {k:r[k]for k in ('status','cases','rows','states','symbolic_steps','minimum_actual_steps','table_sha256','source_sha256','cases_sha256')}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--full',action='store_true');ap.add_argument('--full-baseline',action='store_true');ap.add_argument('--output-dir',type=Path,required=True);a=ap.parse_args()
 require(__debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'),'Assertions must remain enabled')
 out=a.output_dir.resolve();require(out!=ROOT and ROOT not in out.parents,'Choose an output directory outside the proof packet');out.mkdir(parents=True,exist_ok=True);(out/'logs').mkdir(exist_ok=True)
 result={'status':'IN_PROGRESS','mode':'full'if a.full else'quick','fresh_local_Rocq_build':False,'phases':[]};start=time.monotonic()
 def save():result['seconds']=time.monotonic()-start;(out/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
 def run(label,script,*args):
  print(label,flush=True);log=out/'logs'/f'{label}.log'
  with log.open('w')as f:r=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
  require(r.returncode==0,f'{label} failed: '+log.read_text()[-2000:]);result['phases'].append(label);save()
 try:
  manifest=json.loads((ROOT/'manifest.json').read_text())
  for name,digest in manifest['files'].items():
   p=Path(name);require(not p.is_absolute()and'..'not in p.parts,'Unsafe manifest path');require(sha(ROOT/p)==digest,'Manifest mismatch: '+name)
  result['manifest_files_checked']=len(manifest['files'])
  run('baseline226',ROOT/'baseline226/reproduce.py',*([]if a.full_baseline else['--quick']),'--output-dir',out/'baseline226')
  run('construct225',ROOT/'verification/build225.py','--output-dir',out/'candidate225')
  for name in ('candidate225.tm','candidate225.klabels.tm','k225.tm','sites225.json','rotated226.tm','construction.json','renumbering225.json','startup225.json','local_fold225.json'):
   require((out/'candidate225'/name).read_bytes()==(ROOT/'results'/name).read_bytes(),'Reconstructed artifact mismatch: '+name)
  run('independent225',ROOT/'verification/check225.py','--output-dir',out/'independent225','--results-dir',out/'candidate225')
  result['stored_runtime']=audit_runtime(ROOT/'results/runtime225.json',out/'candidate225/candidate225.tm',out/'candidate225/sites225.json')
  if a.full:
   run('runtime225',ROOT/'baseline226/verification/runtime.py',out/'candidate225/candidate225.tm',out/'candidate225/sites225.json',out/'runtime225.json')
   result['fresh_runtime']=audit_runtime(out/'runtime225.json',out/'candidate225/candidate225.tm',out/'candidate225/sites225.json')
   require((out/'runtime225_cases.json').read_bytes()==(ROOT/'results/runtime225_cases.json').read_bytes(),'Fresh runtime case array changed')
  result.update(status='FULL_REPLAY_PASS'if a.full else'QUICK_REPLAY_PASS',working_states=225,rows=450,source_leaves=5121,source_dag_nodes=211,maximum_zero_run=6,maximum_depth=38,startup_steps=409835,scope='Executable ordinary mathematical certificates with pinned inherited formal evidence; no new Rocq kernel build.');save();print(json.dumps(result,indent=2),flush=True)
 except Exception as e:result.update(status='FAIL',error=repr(e));save();raise
if __name__=='__main__':main()
