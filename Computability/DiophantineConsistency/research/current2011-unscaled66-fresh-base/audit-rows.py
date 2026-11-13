#!/usr/bin/env python3
"""Compare the graph definition to the independently audited historical client."""
import hashlib
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
here = Path(__file__).resolve().parent
old = here.parent / 'current2011-unscaled66-model/Current2011Unscaled66.lean'
new = here / 'Current2011Unscaled66Fresh.lean'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
if sha(old) != '151dae72af79bf7d4714329ca3bda7a4b3308bb3e3a40d7ae3c14ae16bacd9a3':
    raise SystemExit('historical source mismatch')
def graph(p):
    return p.read_text().split('def expressionAt (p : Fin 4 → ℤ) : Expr (Fin 14) :=', 1)[1].split('\nsection Eval', 1)[0]
if graph(old) != graph(new):
    raise SystemExit('graph text mismatch')
print('PASS exact 66-row graph definition equals independently audited source')
print('new-source-sha256', sha(new))
