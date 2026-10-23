#!/usr/bin/env python3
"""Fresh-copy replay of the two inspected late archive root drivers."""
from pathlib import Path
import concurrent.futures,hashlib,json,os,platform,shutil,subprocess,sys,tempfile,time
BASE=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
ROOTS={'separated':BASE/'wave8_late_inputs/ConZFC_Separated_Degrees_2026-10-23/con-zfc-separated-degrees-2026-10-23','free_coordinate':BASE/'wave8_late_inputs/ConZFC_Free_Coordinate_2026-10-23/con_zfc_free_coordinate_2026-10-23'}
SCRIPTS={'separated':'reproduce.py','free_coordinate':'verify_all.py'}
def hashes(root):return {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()for p in root.rglob('*')if p.is_file()and'__pycache__'not in p.parts and p.suffix!='.pyc'}
inputs={name:hashes(root)for name,root in ROOTS.items()};(OUT/'LATE_REPLAY_INPUT_HASHES.json').write_text(json.dumps(inputs,indent=2)+'\n')
def run(case):
 name,opt=case;tag=name+('_optimized'if opt else'_normal');tmp=Path(tempfile.mkdtemp(prefix='late_original_'+tag+'_'));work=tmp/'archive';shutil.copytree(ROOTS[name],work,ignore=shutil.ignore_patterns('__pycache__','*.pyc'));before=hashes(work)
 env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1';env.pop('PYTHONOPTIMIZE',None);start=time.monotonic()
 cp=subprocess.run([sys.executable]+(['-O']if opt else[])+[SCRIPTS[name]],cwd=work,env=env,text=True,capture_output=True,timeout=1200)
 (OUT/('LATE_REPLAY_'+tag+'.stdout.txt')).write_text(cp.stdout);(OUT/('LATE_REPLAY_'+tag+'.stderr.txt')).write_text(cp.stderr)
 after=hashes(work);changed=[p for p,h in before.items()if after.get(p)!=h]
 expected=name=='separated'and opt
 status='EXPECTED_REJECTION'if expected and cp.returncode!=0 and 'Run without -O/-OO' in cp.stderr else'PASS'if not expected and cp.returncode==0 else'FAIL'
 r={'archive':name,'optimized':opt,'root_script':SCRIPTS[name],'returncode':cp.returncode,'status':status,'seconds':round(time.monotonic()-start,3),'workcopy':str(work),'stdout_sha256':hashlib.sha256(cp.stdout.encode()).hexdigest(),'stderr_sha256':hashlib.sha256(cp.stderr.encode()).hexdigest(),'stdout_tail':cp.stdout.splitlines()[-15:],'stderr_tail':cp.stderr.splitlines()[-20:],'changed_existing_files':changed,'new_files':sorted(set(after)-set(before))}
 for path in ['certificates/REPRODUCTION.json','generated/METRICS.json','short/generated/AUDIT.json','nine/VERIFICATION.json']:
  p=work/path
  if p.is_file():(OUT/('LATE_REPLAY_'+tag+'__'+path.replace('/','__'))).write_bytes(p.read_bytes())
 print(json.dumps(r),flush=True);return r
with concurrent.futures.ThreadPoolExecutor(max_workers=4)as pool:results=list(pool.map(run,[(n,opt)for n in ROOTS for opt in [False,True]]))
unchanged={n:hashes(r)==inputs[n]for n,r in ROOTS.items()}
receipt={'scope':'Original root drivers on four fresh archive copies, after reading root programs and inspecting all Python AST import/process/write operations. No frozen wave8 family modified. No kernel or universal theorem claim.','python':platform.python_version(),'runs':results,'original_extracted_trees_unchanged':unchanged,'status':'PASS'if all(r['status']in['PASS','EXPECTED_REJECTION']for r in results)and all(unchanged.values())else'FAIL'}
(OUT/'LATE_REPLAY_RESULTS.json').write_text(json.dumps(receipt,indent=2)+'\n');print('FINAL',receipt['status'],flush=True)
