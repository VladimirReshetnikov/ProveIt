#!/usr/bin/env python3
"""Syntactic witness-degree upper bound for the generated graph."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B without optimization')
p=Path(__file__).resolve().parent/'graph.json';raw=p.read_bytes()
if hashlib.sha256(raw).hexdigest()!='875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806':raise RuntimeError('graph drift')
g=json.loads(raw);deg={n:1 for n in g['witnesses']};deg.update({n:0 for n in g['fixed_numerals']})
for n,op,a,b in g['source']:
    x=deg[a] if isinstance(a,str) else 0;y=deg[b] if isinstance(b,str) else 0
    deg[n]=x+y if op=='*' else max(x,y)
expected={'A0':22,'M':38,'W':22,'Na':30,'Lt':2,'polynomial':104}
if {n:deg[n] for n in expected}!=expected:raise RuntimeError('upper bounds differ')
print(json.dumps({'status':'PASS_SYNTACTIC_UPPER_BOUND','upper_bounds':expected,'scope':'Total degree in witness variables, treating ports as coefficients; exactness requires separate nonzero leading coefficient evidence.'},sort_keys=True))
