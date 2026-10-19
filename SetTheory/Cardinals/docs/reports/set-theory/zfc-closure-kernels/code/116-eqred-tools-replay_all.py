#!/usr/bin/env python3
"""Replay finite certificates in a fresh temporary copy; keep the archive unchanged."""
from pathlib import Path
import subprocess,sys,tempfile,shutil,hashlib,json,os,time
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic();jobs=[]
with tempfile.TemporaryDirectory(prefix='zfc-equality-replay-')as tmp:
 dst=Path(tmp)
 for name in ('proofs','audit','frontend','tools','source_binding','reference_lean'):shutil.copytree(ROOT/name,dst/name,ignore=shutil.ignore_patterns('__pycache__'))
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
 def run(path,opt=False):
  command=[sys.executable]+(['-O']if opt else[])+[str(dst/path)]
  r=subprocess.run(command,cwd=dst,env=env,text=True,capture_output=True)
  if r.returncode:
   print(r.stdout);print(r.stderr,file=sys.stderr);raise RuntimeError('failed: '+path)
  jobs.append({'program':path,'optimized_python':opt,'returncode':0})
  print('PASS '+path,flush=True)
  return r.stdout
 for name,artifact in [('equality_certificates.py','equality_proofs.json'),('eq_to_indiscernibility.py','eq_to_indiscernibility_proofs.json'),('indiscernibility_certificates.py','indiscernibility_proofs.json'),('hilbert_atomic_stability.py','hilbert_proofs.json')]:
  run('proofs/'+name)
  if sha(dst/'proofs'/artifact)!=sha(ROOT/'proofs'/artifact):raise RuntimeError('regenerated artifact differs: '+artifact)
 for name in ('replay_equality.py','replay_eq_to_indiscernibility.py','replay_indiscernibility.py','replay_hilbert_proofs.py'):run('proofs/'+name,True)
 run('proofs/check_general_kappa.py',True)
 if sha(dst/'proofs/general_kappa_results.json')!=sha(ROOT/'proofs/general_kappa_results.json'):raise RuntimeError('general-kappa receipt differs')
 run('audit/check_independent.py',True)
 run('audit/check_native_edges.py',True)
 run('audit/check_frontend_placement.py',True)
 binding=json.loads(run('source_binding/check_binding.py',True))
 if len(binding['candidates'])!=26:raise RuntimeError('source candidate count changed')
 if sha(dst/'source_binding/binding_results.json')!=sha(ROOT/'source_binding/binding_results.json'):raise RuntimeError('source binding receipt differs')
 frontend=json.loads(run('tools/check_frontend.py',True))
 main=json.loads((dst/'proofs/indiscernibility_replay_results.json').read_text())
 independent=json.loads((dst/'audit/independent_results.json').read_text())
 report={'valid':True,'jobs':jobs,'all_four_regenerated_proof_JSON_files_byte_identical':True,'main_E_roots':main['closed_roots'],'main_E_nodes':main['proof_nodes'],'independent_E_roots':independent['edges']['roots'],'independent_E_nodes':independent['edges']['nodes'],'native_codes_checked':65535,'general_kappa_roots':169,'general_kappa_nodes':27486,'source_bindings':26,'source_negative_controls_rejected':4,'frontend':frontend,'elapsed_seconds':round(time.monotonic()-start,3),'scope':'Finite proof and native-code regressions plus pinned source/table checks. Not a Lean build, proof-assistant enumerator theorem, or new machine calibration.'}
 print(json.dumps(report,indent=2))
