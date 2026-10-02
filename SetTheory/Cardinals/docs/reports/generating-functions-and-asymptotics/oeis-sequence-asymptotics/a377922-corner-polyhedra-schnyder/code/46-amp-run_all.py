"""Verify new algebra and replay Foundation checks in an isolated temporary copy."""
from pathlib import Path
import hashlib,json,platform,shutil,subprocess,sys,tempfile
import sympy
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'results'
OUT.mkdir(exist_ok=True)
records=[]
def run(script,log_name):
    result=subprocess.run([sys.executable,str(script)],text=True,capture_output=True)
    (OUT/log_name).write_text(result.stdout)
    print(result.stdout.rstrip())
    if result.returncode:
        print(result.stderr,file=sys.stderr)
        raise SystemExit(result.returncode)
    return {'exit_code':0,'status':'PASS'}
for name in ['verify_foundation.py','verify_addendum.py']:
    print('Running '+name,flush=True)
    records.append({'script':'scripts/'+name,**run(ROOT/'scripts'/name,name.removesuffix('.py')+'.stdout.txt')})
with tempfile.TemporaryDirectory(prefix='bimodal-foundation-check-') as temporary:
    clone=Path(temporary)/'foundation'
    shutil.copytree(ROOT/'foundation',clone)
    print('Replaying four Foundation programs in a temporary copy',flush=True)
    records.append({'script':'foundation/scripts/run_all.py','execution':'isolated temporary copy',**run(clone/'scripts/run_all.py','foundation-replay.stdout.txt')})
    exact_results=['symbolic-checks.json','independent-corner-checks.json','independent-schnyder-checks.json','schnyder-enumeration.json']
    for name in exact_results:
        assert (clone/'results'/name).read_bytes()==(ROOT/'foundation/results'/name).read_bytes(),name
    records.append({'check':'Foundation exact result byte comparison','files':len(exact_results),'status':'PASS'})
summary={'status':'PASS','python':platform.python_version(),'sympy':sympy.__version__,'checks':records,
         'scope':'Exact finite checks and unchanged Foundation integrity; asymptotic proofs and their review are separate.'}
(OUT/'verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('PASS: all addendum checks and isolated Foundation replay')
