#!/usr/bin/env python3
"""Exact215 fresh runtime wrapper: frozen eight inputs, fresh output, bounded process.
Only the runtime leaf is executed. Logical calibration and independent audits are separate.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,shutil,subprocess,sys,time,traceback

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--candidate',type=Path,default=Path(__file__).resolve().parents[1]);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 root=a.candidate.resolve();out=a.out.resolve();pins=json.loads((root/'code/frozen-runtime-inputs.json').read_text())
 assert pins['working_states']==215 and pins['expected_cases']==6176
 # Refuse reused output before any inputs are copied or child code imported.
 out.mkdir(parents=True,exist_ok=False)
 actual={'status':'FAIL','scope':'Fresh quantified primitive runtime plus checker startup; independent blank/source/calibration reviews are separate.','working_states':215,'expected_cases':6176,'timeout_seconds':360,'preflight_limit':500000,'python':sys.version,'wrapper_sha256':sha(Path(__file__))}
 try:
  for row in pins['files']:
   src=root/row['source'];assert sha(src)==row['sha256'],('input changed',row['source'])
   dst=out/row['copy'];dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);assert sha(dst)==row['sha256']
  def hashes():return{row['copy']:sha(out/row['copy'])for row in pins['files']}
  before=hashes();actual['before']=before;dump(out/'before.json',before)
  spec=importlib.util.spec_from_file_location('k215_copied_validate',out/'code/validate_native.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
  st=mod.startup(mod.s.r.table(out/'candidate.native.tm'),limit=500000);dump(out/'preflight.json',st)
  actual['preflight']={k:v for k,v in st.items()if k not in('trace','one_cells')}
  print('PREFLIGHT',json.dumps(actual['preflight']),flush=True)
  assert st['status']=='CALIBRATED_DIRTY_ROOT_SEED'
  assert(st['steps'],st['state'],st['head'],st['gap'],st['registers'],st['spares'])==(95714,84,-8,1,[4,0,0,0,0,0,0,0,0],[1]*40)
  cmd=[sys.executable,'-B',str(out/'code/validate_native.py'),str(out/'candidate.native.tm'),str(out/'sites.json'),str(out/'runtime')];actual['argv']=cmd
  started=time.monotonic()
  with(out/'runtime.log').open('w')as log:
   try:r=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=360);actual['returncode']=r.returncode;actual['timed_out']=False
   except subprocess.TimeoutExpired:actual['returncode']=None;actual['timed_out']=True
  actual['elapsed_seconds']=time.monotonic()-started;actual['after']=hashes()
  rp=out/'runtime/runtime.json';report=json.loads(rp.read_text())if rp.exists()else{}
  actual['runtime']={k:v for k,v in report.items()if k!='blocks'}
  assert actual['returncode']==0 and not actual['timed_out'] and actual['before']==actual['after']
  assert report.get('status')=='UNIVERSAL_MATHEMATICAL_PASS' and report.get('proved_cases')==report.get('expected_cases')==6176 and report.get('working_states')==215 and not report.get('failures')
  assert report['table_sha256']==before['candidate.native.tm'] and report['sites_sha256']==before['sites.json']
  assert json.loads((out/'runtime/startup.json').read_text())==st
  cases=json.loads((out/'runtime/runtime_cases.json').read_text());assert len(cases)==6176
  actual['status']='PASS'
 except Exception as exc:
  actual['exception']={'type':type(exc).__name__,'message':str(exc)};(out/'failure.log').write_text(traceback.format_exc())
 finally:
  dump(out/'actual.json',actual);print(json.dumps(actual,indent=2),flush=True)
 if actual['status']!='PASS':raise SystemExit(1)
if __name__=='__main__':main()
