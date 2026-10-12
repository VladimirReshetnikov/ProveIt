#!/usr/bin/env python3
"""Run the delivered exact and numerical suites from any working directory."""
from pathlib import Path
import argparse,json,platform,subprocess,sys,time
import sympy,mpmath
ROOT=Path(__file__).resolve().parents[1]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exact-only',action='store_true')
    args=parser.parse_args(); records=[]
    suites=['exact.py'] if args.exact_only else ['exact.py','numerical.py']
    for name in suites:
        start=time.perf_counter()
        completed=subprocess.run([sys.executable,str(ROOT/'verification'/name)],cwd=ROOT,text=True,capture_output=True)
        (ROOT/'results'/f'{name[:-3]}_run.log').write_text(completed.stdout+completed.stderr)
        print(completed.stdout,end='');print(completed.stderr,end='',file=sys.stderr)
        records.append({'suite':name,'exit_code':completed.returncode,'elapsed_seconds':round(time.perf_counter()-start,3)})
        if completed.returncode:
            (ROOT/'results'/'run_all.json').write_text(json.dumps({'status':'failed','suites':records},indent=2))
            return completed.returncode
    (ROOT/'results'/'environment.json').write_text(json.dumps({'python':sys.version,'platform':platform.platform(),'sympy':sympy.__version__,'mpmath':mpmath.__version__},indent=2))
    (ROOT/'results'/'run_all.json').write_text(json.dumps({'status':'passed','suites':records},indent=2))
    return 0
if __name__=='__main__':raise SystemExit(main())
