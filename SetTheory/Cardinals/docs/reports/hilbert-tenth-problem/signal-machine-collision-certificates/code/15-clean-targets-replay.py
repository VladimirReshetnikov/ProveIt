#!/usr/bin/env python3
"""Replay the portable construction in an isolated temporary copy."""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--receipt',type=Path);a=p.parse_args()
root=Path(__file__).resolve().parent
if (root/'SHA256SUMS').exists():subprocess.run([sys.executable,str(root/'verify_manifest.py')],check=True)
start=time.monotonic();results=[]
with tempfile.TemporaryDirectory(prefix='clean-target-replay-') as temp:
    stage=Path(temp)
    for name in ('clean_targets.py','check_clean_targets.py','test_clean_targets.py','test_affine_lift.py'):shutil.copy2(root/name,stage/name)
    for name in ('vendor','examples','audit'):shutil.copytree(root/name,stage/name,ignore=shutil.ignore_patterns('__pycache__'))
    (stage/'receipts').mkdir()
    commands=[['test_clean_targets.py'],['-O','test_clean_targets.py'],['test_affine_lift.py'],['-O','test_affine_lift.py'],['audit/audit_actual_ca.py'],['audit/audit_certificates.py'],['audit/audit_witness_lift.py'],['audit/audit_lift_name_collisions.py'],['clean_targets.py','export','examples/chain_request.json','cli-certificate.json','--expanded'],['clean_targets.py','witness','cli-certificate.json','cli-witness.json'],['check_clean_targets.py','cli-certificate.json','cli-witness.json']]
    for cmd in commands:
        r=subprocess.run([sys.executable,*cmd],cwd=stage,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},capture_output=True,text=True)
        results.append({'command':'python '+' '.join(cmd),'returncode':r.returncode})
        if r.returncode:print(r.stdout,r.stderr);raise SystemExit('FAILED: '+str(cmd))
        print('PASS: python '+' '.join(cmd),flush=True)
    for n in ('certificate','witness'):
        if (stage/f'cli-{n}.json').read_bytes() != (root/f'examples/chain_{n}.json').read_bytes():raise SystemExit('literal CLI example mismatch: '+n)
    for n in ('chain_certificate.json','chain_witness.json','chain_request.json','chain_receipt.json'):
        if (stage/'examples'/n).read_bytes() != (root/'examples'/n).read_bytes():raise SystemExit('regenerated example mismatch: '+n)
    receipts={}
    for f in [stage/'receipts/test_clean_targets.json',stage/'receipts/affine_lift.json',*sorted((stage/'audit').glob('*receipt.json'))]:
        receipts[f.name]=json.loads(f.read_text())
    out={'status':'passed','portable_fresh_copy':True,'python':sys.version.split()[0],'elapsed_seconds':round(time.monotonic()-start,3),'commands':results,'literal_examples_byte_identical':True,'subject_sha256':{n:hashlib.sha256((root/n).read_bytes()).hexdigest() for n in ('clean_targets.py','check_clean_targets.py','test_clean_targets.py','test_affine_lift.py')},'receipts':receipts}
if a.receipt:a.receipt.write_text(json.dumps(out,indent=2)+'\n')
print('PASS: all portable replays and literal examples')
