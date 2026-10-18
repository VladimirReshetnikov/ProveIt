from pathlib import Path
import argparse,hashlib,json,os,signal,shutil,subprocess,sys,time
ap=argparse.ArgumentParser();ap.add_argument('--expanded',action='store_true');args=ap.parse_args()
ROOT=Path('/tmp/zfc243-root-replay')
ORIG=Path('/tmp/zfc243-combined-candidate')
REF=Path('/tmp/zfc244-rotation-root-replay/copy/reference/baseline245')
if not args.expanded:
 assert not ROOT.exists();ROOT.mkdir()
 (ROOT/'candidate').mkdir()
 for name in ['machine_old.tm','machine.tm','renumbering.json','sites_logical.json','sites_physical.json']:
  shutil.copyfile(ORIG/name,ROOT/'candidate'/name)
 shutil.copytree(ORIG/'adapters',ROOT/'adapters')
 shutil.copyfile(__file__,ROOT/'replay.py')
else:
 assert (ROOT/'quick-verification.json').is_file()
C=ROOT/'candidate';A=ROOT/'adapters';P=[sys.executable,'-B']
jobs=[('expanded',P+[str(A/'check_runtime_combined243.py'),'--reference',str(REF),'--candidate',str(C),'--expanded'])] if args.expanded else [
 ('blank',P+[str(A/'check_combined243_blank.py'),'--table',str(C/'machine_old.tm'),'--baseline',str(REF/'certificate/machine_old.tm'),'--reference',str(REF),'--output',str(ROOT/'blank')]),
 ('affine',P+[str(A/'check_runtime_combined243.py'),'--reference',str(REF),'--candidate',str(C)]),
 ('literal',P+[str(A/'check_combined243_literal.py'),'--candidate',str(C)])]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tracked=[C/n for n in ['machine_old.tm','machine.tm','renumbering.json','sites_logical.json','sites_physical.json']]+list(A.glob('*.py'))+[Path(__file__)]
before={str(p):sha(p) for p in tracked};rows=[]
for name,cmd in jobs:
 assert not (ROOT/(name+'.stdout.log')).exists()
 t=time.monotonic()
 with (ROOT/(name+'.stdout.log')).open('wb')as stdout,(ROOT/(name+'.stderr.log')).open('wb')as stderr:
  child=subprocess.Popen(cmd,cwd=ROOT,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},stdout=stdout,stderr=stderr,start_new_session=True)
  timeout=False
  try:rc=child.wait(timeout=600)
  except subprocess.TimeoutExpired:
   timeout=True;os.killpg(child.pid,signal.SIGKILL);rc=child.wait()
  row={'job':name,'command':cmd,'exit_code':rc,'timeout':timeout,'seconds':time.monotonic()-t};rows.append(row)
 (ROOT/('expanded-execution.json' if args.expanded else 'quick-execution.json')).write_text(json.dumps(rows,indent=2)+'\n')
 print(json.dumps(row),flush=True)
 if rc or timeout:sys.exit(1)
after={str(p):sha(p) for p in tracked};assert before==after
if args.expanded:
 e=json.loads((C/'expanded-runtime.json').read_text())
 assert e['complete'] and e['counts']['cases']==8390 and e['unused_rows']==[[27,1]]
 assert e['literal_rows_covered']==485 and e['positive_progress_checked']
 summary={'status':'PASS_COMBINED243_EXPANDED_RUNTIME','counts':e['counts'],'rows_covered':485,'unused_rows':[[27,1]],'scope':'Fresh expanded whole-frame symbolic replay; no Lean or PA endpoint.'}
else:
 b=json.loads((ROOT/'blank/independent-blank.json').read_text());l=json.loads((C/'literal-regression.json').read_text());e=json.loads((C/'affine-runtime.json').read_text())
 assert b['working_states']==243 and l['cases']==e['counts']['cases']==8390
 assert b['table_sha256']==sha(C/'machine.tm')
 summary={'status':'PASS_COMBINED243_BLANK_AFFINE_LITERAL','blank_steps':b['blank_steps'],'literal_steps':l['literal_steps'],'cases':8390,'scope':'Exact blank prefix, affine proof-certificate replay, finite literal fixtures; expanded proof separate.'}
summary.update(before=before,after=after,commands=rows)
(ROOT/('expanded-verification.json'if args.expanded else'quick-verification.json')).write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items()if k not in ['before','after','commands']}),flush=True)
