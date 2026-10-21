from pathlib import Path
import json,subprocess,shutil,sys,time,zipfile,stat
import argparse
parser=argparse.ArgumentParser(description='Replay only the five selected K217 leaves on a fresh copy.')
parser.add_argument('--packet',type=Path,required=True,help='Recovered K217_Dominated_Continuation_2026-10-20 directory')
parser.add_argument('--output',type=Path,required=True,help='New scratch directory')
args=parser.parse_args()
ROOT=args.packet.resolve()
OUT=args.output.resolve();OUT.mkdir(exist_ok=False)
P=OUT/'packet';shutil.copytree(ROOT,P);B=OUT/'parent'
with zipfile.ZipFile(P/'parent/K218_Dominated_Rho8_2026-10-20.zip')as z:
 for i in z.infolist():
  p=Path(i.filename);assert not p.is_absolute()and '..'not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
 z.extractall(B)
B=B/'K218_Dominated_Rho8_2026-10-20';(OUT/'logs').mkdir()
jobs=[('reconstruct',[P/'code/reconstruct217.py','--base',B,'--output',OUT/'rebuilt'],60,OUT/'rebuilt/construction.json','DETERMINISTIC_K217_RECONSTRUCTION_PASS'),('source-fold',[P/'code/audit_source_fold.py','--base',B,'--candidate',P/'machine','--out',OUT/'source-fold.json'],60,OUT/'source-fold.json','INDEPENDENT_SOURCE_ROTATION_AND_ALL_TAPE_FOLD_PASS'),('blank',[P/'code/audit_blank.py','--directory',P/'machine','--canonical',P/'machine/k217.tm','--output',OUT/'blank.json'],60,OUT/'blank.json','INDEPENDENT_FINITE_STARTUP_AND_TABLE_PASS'),('local-fold',[P/'code/check_joint_fold.py','--old',P/'machine/unfolded218.native.tm','--new',P/'machine/k217.native.tm','--keep','69','--drop','400','--radius','7','--fuel','97','--output',OUT/'fold-window.json'],90,OUT/'fold-window.json',None),('runtime',[B/'binary/code/validate_native.py',P/'machine/k217.native.tm',P/'machine/sites217.json',OUT/'runtime'],300,OUT/'runtime/runtime.json','UNIVERSAL_MATHEMATICAL_PASS')]
result={'status':'RUNNING','scope':'Five selected fresh leaves. No wrapper, manifest, parent verification, proof assistant, broad search or logical certificate replay. Source149 parent calibration and fresh eight jobs inherited.','jobs':[]}
for name,args,cap,receipt,expected in jobs:
 cmd=[sys.executable,'-B',*map(str,args)];start=time.monotonic()
 with(OUT/'logs'/(name+'.stdout')).open('w')as o,(OUT/'logs'/(name+'.stderr')).open('w')as e:
  try:p=subprocess.run(cmd,cwd=P,stdout=o,stderr=e,timeout=cap);rc=p.returncode;timed=False
  except subprocess.TimeoutExpired:rc=None;timed=True
 data=json.loads(receipt.read_text())if receipt.exists()else None
 ok=rc==0 and data is not None and(expected is None or data.get('status')==expected)
 result['jobs'].append({'name':name,'argv':cmd,'cwd':str(P),'timeout_seconds':cap,'exit_code':rc,'timed_out':timed,'seconds':time.monotonic()-start,'receipt':str(receipt),'status':None if data is None else data.get('status'),'accepted':ok});result['status']='RUNNING'if ok else'FAIL';(OUT/'actual.json').write_text(json.dumps(result,indent=2)+'\n');print(name,ok,result['jobs'][-1]['status'],flush=True)
 if not ok:break
else:result['status']='FIVE_SELECTED_LEAVES_PASS'
(OUT/'actual.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],flush=True)
