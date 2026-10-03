"""Run all exact checks and write a reproducible execution receipt. Stdlib only."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,platform,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
scripts=['replay_tests.py','focused_tests.py','verify_saved_examples.py','regression_extensions.py','export_sos.py']
records=[]
started=datetime.now(timezone.utc).isoformat()
for script in scripts:
    t=time.monotonic()
    result=subprocess.run([sys.executable,str(ROOT/script)],cwd=ROOT,text=True,capture_output=True)
    log=ROOT/(Path(script).stem+'_stdout.txt')
    log.write_text(result.stdout+('\nSTDERR\n'+result.stderr if result.stderr else ''))
    records.append({'script':script,'exit_code':result.returncode,'elapsed_seconds':round(time.monotonic()-t,3),'stdout_file':log.name})
    print(script+': '+('passed' if result.returncode==0 else 'FAILED'),flush=True)
    if result.returncode:
        print(result.stdout+result.stderr)
        raise SystemExit(result.returncode)
files=sorted(p for p in ROOT.iterdir() if p.is_file() and p.name!='run_receipt.json')
receipt={'status':'passed','started_utc':started,'completed_utc':datetime.now(timezone.utc).isoformat(),'python':platform.python_version(),'platform':platform.platform(),'scripts':records,'sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in files},'scope':'Finite exact arithmetic corroboration. Not formal verification, proof of universality, or a fixed-arity unbounded-history certificate.'}
(ROOT/'run_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
