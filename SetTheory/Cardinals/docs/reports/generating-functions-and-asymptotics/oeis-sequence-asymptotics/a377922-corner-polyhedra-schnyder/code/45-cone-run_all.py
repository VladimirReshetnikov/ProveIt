"""Run every exact check from any working directory and record a summary."""
from pathlib import Path
import json, platform, subprocess, sys
import sympy
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'results'
OUT.mkdir(exist_ok=True)
scripts=['verify_symbols.py','independent_corner_checks.py','independent_schnyder_checks.py','enumerate_schnyder.py']
records=[]
for name in scripts:
    print('Running '+name, flush=True)
    result=subprocess.run([sys.executable,str(ROOT/'scripts'/name)], cwd=ROOT, text=True, capture_output=True)
    (OUT/(name.removesuffix('.py')+'.stdout.txt')).write_text(result.stdout)
    if result.stderr:
        (OUT/(name.removesuffix('.py')+'.stderr.txt')).write_text(result.stderr)
    records.append({'script':'scripts/'+name,'exit_code':result.returncode,'status':'PASS' if result.returncode==0 else 'FAIL'})
    print(result.stdout.rstrip())
    if result.returncode:
        print(result.stderr,file=sys.stderr)
        raise SystemExit(result.returncode)
summary={'status':'PASS','python':platform.python_version(),'sympy':sympy.__version__,'checks':records,
         'scope':'Exact algebra and finite enumeration only; the probabilistic proof is in article.tex/article.pdf.'}
(OUT/'verification-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print('PASS: all verification scripts')
