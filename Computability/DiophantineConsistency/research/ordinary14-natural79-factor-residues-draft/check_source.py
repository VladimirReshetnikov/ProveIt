#!/usr/bin/env python3
"""Bounded literal factor AST and source composition audit; no Lean run."""
import hashlib,json
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1]
files={
 'shape':(P/'Natural79ResidueShapes.lean','b4d60c7db8fb92cac53f38f81414a6319d8979ccbcb575d2e29e49fa5a51fd38'),
 'client':(P/'Natural79ConcreteUnits.lean','253421a5ac864a94a9926472d9c469c2997d6581cded0aaa3fda27b2830d118d'),
 'graph':(D/'research/ordinary14-natural-forced-w79-lean-draft/P79NaturalForcedW.lean','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36'),
 'graph_json':(D/'research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'),
 'unit':(D/'research/ordinary14-natural79-zero-w-unit-draft/Natural79ZeroWUnits.lean','2570ae56ca0c4081b9442d768d94a4ded2cb365b74ed66bfe040c202b65aec1c'),
 'residue':(D/'research/ordinary14-74-factor-residues-draft/FactorResidues74.lean','368e6e5f3db5693db859fdc85a9441f0d6378969563eec289c2c121e6b4b1d60')}
s={}
for n,(p,h) in files.items():
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,n;s[n]=b.decode()
def literal(t,end):
 a=t.index('  let n_J : Expr (Fin 14) := .var 0'); b=t.index(end,a);return t[a:b]
assert literal(s['graph'],'  -- END LITERAL GRAPH')==literal(s['shape'],'  ⟨U,a,c,Dstar,I,V⟩')
assert '⟨U,a,c,Dstar,I,V⟩' in s['shape']
assert '⟨F0, F1, Fa, Fs, guard, out, qF, C, G, R⟩' in s['graph']
for n in ('main_shape','aux_shape','strong_shape','restricted_residues'): assert 'theorem '+n in s['shape']
for n in ('main_ne','aux_ne','strong_ne'): assert 'theorem '+n in s['residue']
for tok in ('Natural79ResidueShapesDraft.restricted_residues p v',
            'Natural79ZeroWUnitsDraft.units_of_zero_w_zero p v hz hw hm ha hs'):
 assert tok in s['client'],tok
assert 'sorry' not in s['shape']+s['client'] and 'admit' not in s['shape']+s['client']
# Compare exact unexpanded expression trees of the JSON graph with the
# syntax trees in the three generic factor patterns. This is source-graph
# evidence; the graph's Lean semantics and the `rfl` scripts are unchecked.
a=json.loads(s['graph_json']); e={n:('var',n) for n in a['witnesses']};e.update({n:('port',n) for n in a['fixed_numerals']})
def val(x):return ('num',x) if type(x) is int else e[x]
for n,op,x,y in a['source']:e[n]=(op,val(x),val(y))
def num(x):return ('num',x)
def add(x,y):return ('+',x,y)
def sub(x,y):return ('-',x,y)
def mul(x,y):return ('*',x,y)
u,A,c,d,I,z=e['U'],e['a'],e['c'],e['Dstar'],e['I'],e['V']
f,y=e['n_f'],e['n_y']; delta=add(add(num(3),mul(num(4),A)),mul(A,A));f2minus=sub(mul(f,f),num(1))
assert e['F1']==add(num(1),sub(mul(d,d),mul(mul(u,u),add(num(1),mul(delta,mul(c,c))))))
assert e['Fa']==sub(mul(y,y),mul(mul(delta,f2minus),sub(mul(y,y),mul(z,z))))
assert e['Fs']==add(num(1),sub(mul(I,I),mul(delta,f2minus)))
print(json.dumps({'scope':'literal source/DAG AST correspondence and proposed client calls; no Lean elaboration or iPRA theorem','pinned_files':len(files),'graph_let_blocks_identical':True,'factor_pattern_AST_equalities':3,'residue_hypotheses_discharged_only_in_source_proposal':True},sort_keys=True,indent=2))
