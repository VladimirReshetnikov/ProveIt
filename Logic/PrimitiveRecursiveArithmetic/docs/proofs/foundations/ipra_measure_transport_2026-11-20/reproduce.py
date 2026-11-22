#!/usr/bin/env python3
"""Replay exact checks and optionally the Lean build and LaTeX compilation."""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean',action='store_true')
    p.add_argument('--pdf',action='store_true')
    args=p.parse_args()
    root=Path(__file__).resolve().parent
    out=root/'validation'
    out.mkdir(exist_ok=True)
    counts={}
    for filename,label in [('measure_demo.py','measure_checks'),
                           ('category_topology_checks.py','category_topology_checks'),
                           ('analytic_checks.py','analytic_checks')]:
        run=subprocess.run([sys.executable,str(root/'code'/filename)],
                           text=True,stdout=subprocess.PIPE,check=True)
        result=json.loads(run.stdout)
        if result.get('status')!='passed':
            raise RuntimeError(f'{filename}: failed status')
        (out/(label+'.json')).write_text(json.dumps(result,indent=2)+'\n')
        counts[label]=result['total_assertions']
    print(json.dumps({'status':'passed','assertions':counts,
                      'total_assertions':sum(counts.values())},indent=2))
    if args.lean:
        lake=os.environ.get('LEAN_LAKE_BIN','lake')
        run=subprocess.run([lake,'build'],cwd=root/'lean',text=True,
                           stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (out/'lean_replay.log').write_text(run.stdout)
        print(run.stdout,end='')
        run.check_returncode()
    if args.pdf:
        paper=root/'paper'
        tex='ipra_measure_transport.tex'
        pdftex=os.environ.get('PDFLATEX_BIN','pdflatex')
        if shutil.which(pdftex):
            cmd=[pdftex,'-interaction=nonstopmode','-halt-on-error',tex]
            passes=3
        elif shutil.which('tectonic'):
            cmd=['tectonic','--keep-logs',tex]
            passes=1
        else:
            raise RuntimeError('Install a working pdflatex or tectonic distribution.')
        for _ in range(passes):
            run=subprocess.run(cmd,cwd=paper,text=True,stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT)
            (out/'latex_replay.log').write_text(run.stdout)
            run.check_returncode()
        print('Compiled paper/ipra_measure_transport.pdf')

if __name__=='__main__':
    main()
