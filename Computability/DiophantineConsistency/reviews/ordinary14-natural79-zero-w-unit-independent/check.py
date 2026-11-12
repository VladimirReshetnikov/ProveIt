#!/usr/bin/env python3
"""Independent bounded source and 79-graph arithmetic review; no Lean."""
import hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def pin(path,h):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==h,path;return b.decode()
s=pin('research/ordinary14-natural79-zero-w-unit-draft/Natural79ZeroWUnits.lean','2570ae56ca0c4081b9442d768d94a4ded2cb365b74ed66bfe040c202b65aec1c')
r=pin('research/ordinary14-74-factor-residues-draft/FactorResidues74.lean','368e6e5f3db5693db859fdc85a9441f0d6378969563eec289c2c121e6b4b1d60')
u=pin('Lean/DiophantineConsistency/ArithmeticSignedPairs.lean','ecad260baefecc05bab664a976015d7a76228583c7ec25bcc7536890ef58274d')
f=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean','9e80ae52f5dddd21d50684ebb6ca6556e95ac37905277bc476d251b7bf59f5a4')
graph=pin('research/ordinary14-natural-forced-w79-lean-draft/P79NaturalForcedW.lean','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36')
g=json.loads(pin('research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'))
for name in ('product_of_zero','first_eval_at_w_zero','nonnegative_not_negative_unit','units_of_zero_w_zero','restricted_residues_of_shapes'):assert 'theorem '+name in s
assert 'theorem product5_positive' in u and '(hp : p.1+1≠p.2) (hq : q.1+1≠q.2) (hr : r.1+1≠r.2) (ht : t.1+1≠t.2)' in u
assert 'theorem negative_residue' in f
assert all('theorem '+n in r for n in ('main_ne','aux_ne','strong_ne'))
assert '(hmain : pairResidue' in s and '(haux : pairResidue' in s and '(hstrong : pairResidue' in s
assert '(hm : (P79NaturalForcedW.graph p).main=mainPattern u a c d)' in s
assert '(ha : (P79NaturalForcedW.graph p).aux=auxPattern y z a f)' in s
assert '(hs : (P79NaturalForcedW.graph p).strong=strongPattern i a f)' in s
assert '  ⟨F0, F1, Fa, Fs, guard, out, qF, C, G, R⟩' in graph
rows={n:[op,x,y] for n,op,x,y in g['source']}; assert len(rows)==79
for n,row in {'X':['*','q','n_w'],'E':['*','X','Y'],'ell':['*','E','kY'],'g38':['*','n_r','n_r'],'g40':['*','ell','g30'],'F0':['-','g38','g40'],'P01':['*','F0','F1'],'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],'P01234':['*','P0123','guard'],'out':['-','P01234',1]}.items():assert rows[n]==row
# Check at w=0 over arbitrary signed integer ports/coordinates. These bounded
# controls do not replace the exact graph-structural cut or Lean proof.
rng=random.Random(791991)
for _ in range(150):
 e={n:rng.randint(-2,2) for n in g['witnesses']+g['fixed_numerals']};e['n_w']=0
 for n,op,x,y in g['source']:
  x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
  e[n]=x+y if op=='+' else x-y if op=='-' else x*y
 assert e['F0']==e['n_r']**2
 assert e['out']==e['F0']*e['F1']*e['Fa']*e['Fs']*e['guard']-1
print(json.dumps({'scope':'bounded source interface and graph-cut review; no Lean or model theorem','pinned_sources':6,'w_zero_signed_controls':150,'explicit_residue_pattern_hypotheses':3},sort_keys=True,indent=2))
