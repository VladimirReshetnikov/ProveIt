#!/usr/bin/env python3
"""Deterministic offline reconstruction; standard library only."""
from pathlib import Path
import json,subprocess,sys
R=Path(__file__).resolve().parent
def run(*args):
    flags=['-'+'O'*sys.flags.optimize] if sys.flags.optimize else []
    subprocess.run([sys.executable,*flags,*map(str,args)],cwd=R,check=True)
run(R/'build_source.py');run(R/'build_nine.py')
for domain in ['positive','natural']:run(R/'rewrite_powers.py',R/'generated'/('split_116_'+domain+'.json'))
run(R/'materialize.py');run(R/'verify.py');run(R/'independent_review.py')
