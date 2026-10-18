from pathlib import Path
import hashlib,json,os,signal,subprocess,sys,time

ROOT=Path(__file__).resolve().parent
PACK=ROOT/'copy'
REF=PACK/'reference/baseline245'
OUT=ROOT/'run1'
OUT.mkdir()
PY=[sys.executable,'-B']
jobs=[
 ('construct',PY+[str(PACK/'code/make_qt244.py'),'--reference',str(REF),'--output',str(OUT/'built')]),
 ('source',PY+[str(PACK/'code/check_qt_rotation.py'),'--reference',str(REF),'--output',str(OUT/'source')]),
 ('blank',PY+[str(PACK/'code/check_table_boot.py'),'--table',str(OUT/'built/machine_old.tm'),'--baseline',str(REF/'certificate/machine_old.tm'),'--output',str(OUT/'blank')]),
 ('frames',PY+[str(PACK/'code/check_frames.py'),'--machine',str(OUT/'built'),'--output',str(OUT/'frames.json')]),
 ('affine',PY+[str(PACK/'code/check_runtime.py'),'--reference',str(REF),'--candidate',str(OUT/'built')]),
 ('literal',PY+[str(PACK/'code/check_qt244_literal.py'),'--candidate',str(OUT/'built')]),
 ('expanded',PY+[str(PACK/'code/check_runtime.py'),'--reference',str(REF),'--candidate',str(OUT/'built'),'--expanded'])]
rows=[]
for name,cmd in jobs:
 t=time.monotonic()
 with (OUT/(name+'.stdout.log')).open('wb') as stdout,(OUT/(name+'.stderr.log')).open('wb') as stderr:
  p=subprocess.Popen(cmd,cwd=PACK,stdout=stdout,stderr=stderr,start_new_session=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
  timeout=False
  try: rc=p.wait(timeout=600)
  except subprocess.TimeoutExpired:
   timeout=True;os.killpg(p.pid,signal.SIGKILL);rc=p.wait()
 row={'job':name,'command':cmd,'returncode':rc,'timeout':timeout,'seconds':time.monotonic()-t}
 rows.append(row)
 (OUT/'execution.json').write_text(json.dumps({'jobs':rows,'scope':'Seven primary substantive jobs. Delivery checksum manifests, unrelated research searches and unchanged ancestor replay are omitted.'},indent=2)+'\n')
 print(json.dumps(row),flush=True)
 if rc or timeout:sys.exit(1)
for name in ['machine.tm','machine_old.tm','sites_logical.json','sites_physical.json','renumbering.json','boot.json']:
 assert (OUT/'built'/name).read_bytes()==(PACK/'machine'/name).read_bytes(),name
for name in ['sites_logical.json','sites_physical.json']:
 assert (OUT/'source/right'/name).read_bytes()==(OUT/'built'/name).read_bytes(),name
expanded=json.loads((OUT/'built/expanded-runtime.json').read_text())
assert expanded['counts']['cases']==8390 and expanded['counts']['symbolic_rules']==2312438
assert expanded['literal_rows_covered']==487 and expanded['unused_rows']==[[27,1]]
assert expanded['complete'] and expanded['positive_progress_checked']
summary={'status':'PASS_ROOT_ROTATION244_PRIMARY_REPLAY','jobs':rows,'table_sha256':hashlib.sha256((OUT/'built/machine.tm').read_bytes()).hexdigest(),'cases':8390,'symbolic_rules':2312438,'source_context_edges':json.loads((OUT/'source/right/source_verification.json').read_text())['context_edges_checked'],'blank_steps':407931,'literal':json.loads((OUT/'built/literal-regression.json').read_text()),'scope':'Fresh Python proof-certificate replay and finite literal controls; no new Lean or PA endpoint.'}
(OUT/'verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print(summary['status'],flush=True)
