#!/usr/bin/env python3
"""Exact source-pinned symbolic syzygy and its degree-23 leader."""
import contextlib
import hashlib
import io
import json
import runpy
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
PINS={
 'research/current2011-shear-aux-leading-obstruction/check.py':'a88928fcf775e95c2fb19af1e452e21f119a7e6cb5b179f323b9f36456eb3c70',
 'research/current2011-shear-aux-leading-obstruction/result.json':'2e5b0178a3c0730d3f297ee31a653c2cc8307100e1ed65a40d9f5b6e1b84a8f6',
 'research/current2011-sheared72-46-candidate/polynomial.json':'cfb30017781968c87e1fa7cba5d08a69b555a7c058ddb1e36b313c74b519e78f',
}
for path,h in PINS.items():
 if hashlib.sha256((ROOT/path).read_bytes()).hexdigest()!=h: raise RuntimeError('source pin changed: '+path)
with contextlib.redirect_stdout(io.StringIO()) as output:
 d=runpy.run_path(str(ROOT/'research/current2011-shear-aux-leading-obstruction/check.py'))
if json.loads(output.getvalue())!=json.loads((ROOT/'research/current2011-shear-aux-leading-obstruction/result.json').read_text()):
 raise RuntimeError('predecessor receipt mismatch')
env=d['env']; product=d['product']; plus=d['plus']; literal=d['literal']; leader=d['leader']; degree=d['degree']; power=d['power']; names=d['names']
first=product(literal(8),env['gamma'],env['Nt'],plus(env['N0'],literal(1),-1))
second=product(env['kY'],env['rQW'])
if max(map(degree,first[0]))!=25 or max(map(degree,second[0]))!=25: raise RuntimeError('not degree-25 summands')
if plus(leader(first),leader(second))[0]: raise RuntimeError('degree-25 leaders fail to cancel')
S=plus(first,second); top=leader(S)[0]
if max(map(degree,top))!=23 or len(top)!=28 or S[1]>=23: raise RuntimeError('syzygy leader not certified')
ig=names.index('gamma'); ii=names.index('i')
projected={mon:co for mon,co in top.items() if mon[ig]==0 and mon[ii]==0}
E=leader(env['E']); Y=leader(env['Y']); k=leader(env['k']); W=leader(env['Nt'])
expected=product(literal(-4),E,power(k,3),power(Y,3),W)[0]
if projected!=expected: raise RuntimeError('specialized symbolic leader mismatch')
terms=[]
for mon,co in sorted(top.items()):
 terms.append({'coefficient':co,'powers':{name:e for name,e in zip(names,mon) if e}})
print(json.dumps({'scope':'exact symbolic leaders only; bounded multiplier obstruction uses README proof',
 'summand_degree':25,'syzygy_degree':23,'leader_terms':len(top),
 'degree23_specialized_term_count':len(projected),'discarded_ceiling':S[1],
 'leader':terms},indent=2,sort_keys=True))
