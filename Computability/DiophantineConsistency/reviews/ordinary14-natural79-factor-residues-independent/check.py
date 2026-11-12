#!/usr/bin/env python3
"""Bounded literal factor-pattern and source-client check; no Lean run."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary14-natural79-factor-residues-draft/Natural79ResidueShapes.lean','b4d60c7db8fb92cac53f38f81414a6319d8979ccbcb575d2e29e49fa5a51fd38')
c=pin('research/ordinary14-natural79-factor-residues-draft/Natural79ConcreteUnits.lean','253421a5ac864a94a9926472d9c469c2997d6581cded0aaa3fda27b2830d118d')
g=pin('research/ordinary14-natural-forced-w79-lean-draft/P79NaturalForcedW.lean','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36')
a=json.loads(pin('research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'))
r=pin('research/ordinary14-74-factor-residues-draft/FactorResidues74.lean','368e6e5f3db5693db859fdc85a9441f0d6378969563eec289c2c121e6b4b1d60')
u=pin('research/ordinary14-natural79-zero-w-unit-draft/Natural79ZeroWUnits.lean','2570ae56ca0c4081b9442d768d94a4ded2cb365b74ed66bfe040c202b65aec1c')
# Both files repeat all variables, ports and let declarations exactly.
start='  let n_J : Expr (Fin 14) := .var 0'; end='  -- END LITERAL GRAPH'
assert g[g.index(start):g.index(end)]==s[s.index(start):s.index('  ⟨U,a,c,Dstar,I,V⟩')]
assert '  ⟨F0, F1, Fa, Fs, guard, out, qF, C, G, R⟩' in g
assert '1+(d*d-u*u*(1+((3+4*a)+a*a)*(c*c)))' in r
assert 'y*y-(((3+4*a)+a*a)*(f*f-1))*(y*y-z*z)' in r
assert '1+(i*i-(((3+4*a)+a*a)*(f*f-1)))' in r
for z in ('main_shape','aux_shape','strong_shape','restricted_residues'):assert 'theorem '+z in s
assert '(atoms p).U (atoms p).a (atoms p).c (atoms p).Dstar := by rfl' in s
assert 'auxPattern (.var 11) (atoms p).vroot (atoms p).a (.var 3) := by rfl' in s
assert 'strongPattern (atoms p).I (atoms p).a (.var 3) := by rfl' in s
assert 'Natural79ResidueShapesDraft.restricted_residues p v' in c
assert 'Natural79ZeroWUnitsDraft.units_of_zero_w_zero p v hz hw hm ha hs' in c
signature=c[c.index('theorem units_of_zero_w_zero'):c.index(' := by',c.index('theorem units_of_zero_w_zero'))]
assert '(hz : InternalZero' in signature and '(hw : v 6=0)' in signature
assert not any(x in signature for x in ('(hbeta','(hK','(hgamma','(hmain','(haux','(hstrong'))
# Independently verify the full immutable DAG's literal expression trees.
e={n:('input',n) for n in a['witnesses']};e.update({n:('port',n) for n in a['fixed_numerals']})
def val(x):return ('num',x) if type(x) is int else e[x]
for n,op,x,y in a['source']:e[n]=(op,val(x),val(y))
N=lambda n:('num',n); A=lambda x,y:('+',x,y); S=lambda x,y:('-',x,y); M=lambda x,y:('*',x,y)
U,aa,cc,dd,I,z,f,y=(e[n] for n in ('U','a','c','Dstar','I','V','n_f','n_y'))
delta=A(A(N(3),M(N(4),aa)),M(aa,aa));Q=M(delta,S(M(f,f),N(1)))
assert e['F1']==A(N(1),S(M(dd,dd),M(M(U,U),A(N(1),M(delta,M(cc,cc))))))
assert e['Fa']==S(M(y,y),M(Q,S(M(y,y),M(z,z))))
assert e['Fs']==A(N(1),S(M(I,I),Q))
print(json.dumps({'scope':'bounded literal AST, source signatures and client assumptions; no Lean semantics or axiom closure','pinned_sources':6,'literal_patterns':3,'client_assumptions':['79 zero','w=0']},sort_keys=True,indent=2))
