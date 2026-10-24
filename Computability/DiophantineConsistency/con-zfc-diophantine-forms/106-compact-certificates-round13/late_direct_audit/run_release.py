#!/usr/bin/env python3
"""Ten-run final independent audit suite; only selected release files needed."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent

def main():
    runs=[]
    for mode,flags,suffix in [('normal',[],''),('optimized',['-O'],'.optimized')]:
        jobs=[(BASE/'direct_audit/check_exact.py',[BASE/'direct/forward'],'direct_audit/FORWARD_EXACT_CHECK'+suffix+'.json'),
              (BASE/'direct_audit/check_factoring.py',[],None),
              (ROOT/'check_projected.py',[BASE/'direct/projected'],'late_direct_audit/PROJECTED_CHECK'+suffix+'.json'),
              (ROOT/'check_projected.py',[BASE/'direct/projected_signed_template','--integer',BASE/'direct/projected_integer'],'late_direct_audit/PROJECTED_INTEGER_CHECK'+suffix+'.json'),
              (ROOT/'negative_controls.py',[BASE/'direct/projected',BASE/'direct/projected_signed_template',BASE/'direct/projected_integer'],'late_direct_audit/NEGATIVE_CONTROLS'+suffix+'.json')]
        for script,args,receipt in jobs:
            command=[sys.executable,*flags,str(script),*[str(x) for x in args]]
            if receipt:command += ['--output',str(BASE/receipt)]
            r=subprocess.run(command,capture_output=True,text=True)
            if r.returncode:raise SystemExit(r.stderr or r.stdout or 'audit failed')
            result=json.loads(r.stdout)
            if result.get('status')!='PASS':raise ValueError('non-PASS audit')
            row={'mode':mode,'program':str(script.relative_to(BASE)),'status':'PASS'}
            if receipt:row.update(receipt=receipt,sha256=hashlib.sha256((BASE/receipt).read_bytes()).hexdigest())
            runs.append(row)
    out={'status':'PASS','independent_runs':len(runs),'runs':runs,'scope':'selected1859N/3179Z/2560N exact independent checks; no candidate or upstream executable imports'}
    text=json.dumps(out,indent=2,sort_keys=True)+'\n';(ROOT/'FINAL_REPLAY.json').write_text(text);print(text,end='')
if __name__=='__main__':main()
