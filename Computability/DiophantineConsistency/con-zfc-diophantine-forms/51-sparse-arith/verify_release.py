#!/usr/bin/env python3
"""Rebuild and verify in a temporary copy, preserving the delivered files."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    protected=[]
    for base in ['data','certificates','nine/generated','coefficients/payloads']:
        protected += [p for p in (ROOT/base).rglob('*') if p.is_file()]
    protected += [ROOT/'nine/fixed_values.json']
    before={str(p.relative_to(ROOT)):digest(p) for p in protected}
    scripts=['code/build.py','code/verify_source.py','code/verify_full_circuit.py','code/check_toy.py','code/verify_separator.py','nine/build_nine.py','nine/verify_nine.py','code/verify_nine_interface.py']
    with tempfile.TemporaryDirectory(prefix='proveit_sparse_consistency_') as tmp:
        copy=Path(tmp)/'package';shutil.copytree(ROOT,copy,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        runs=[]
        for script in scripts:
            r=subprocess.run([sys.executable,str(copy/script)],cwd=copy,text=True,capture_output=True)
            if r.returncode:raise RuntimeError(script+' failed:\n'+r.stdout+r.stderr)
            runs.append({'script':script,'mode':'normal','status':'PASS'})
        for script in ['code/verify_source.py','code/verify_full_circuit.py','code/check_toy.py','nine/verify_nine.py','code/verify_nine_interface.py']:
            r=subprocess.run([sys.executable,'-O',str(copy/script)],cwd=copy,text=True,capture_output=True)
            if r.returncode:raise RuntimeError(script+' failed under -O:\n'+r.stdout+r.stderr)
            runs.append({'script':script,'mode':'-O','status':'PASS'})
        different=[p for p,sha in before.items() if not(copy/p).is_file() or digest(copy/p)!=sha]
        if different:raise ValueError('Regeneration differed from delivered artifacts: '+', '.join(different))
    print(json.dumps({'status':'PASS','reproduced_files':len(before),'runs':runs,
      'ten_integer':{'operations':709,'degree':54768104},
      'nine_positive':{'operations':682,'degree':33332620},
      'nine_natural':{'operations':685,'degree':33332620},
      'scope':'Finite identities, byte binding, circuit implementation and exact degree; inherited unbounded theorems remain mathematical dependencies.'},indent=2))
if __name__=='__main__':main()
