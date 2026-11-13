#!/usr/bin/env python3
"""Independent source interface/coordinate audit; no Lean invocation."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parents[2]
files={
'research/ordinary14-natural80-ownzero-norm-draft/Natural80OwnZeroNorm.lean':'670f8a6e7208afccde1051d72b3154990e1347cbf8d51a3845a89f56f81fcb74',
'research/ordinary14-natural80-partial74-bridge-draft/Natural80Partial74.lean':'942674c7951850ae30d457410cfc7a0359fc255831c31a87fc914a5ef3035c16',
'research/ordinary14-natural80-jpos-model-draft/Natural80JPos.lean':'6ac50565b28ac25581504ff28c1b4d6785c61607423d0bed7c22532d6ec8e221',
'research/ordinary14-74-ownzero-product-draft/OwnZeroProduct74.lean':'26404a26b78b3099ddaa407d2eed829d884568821e08a5c7780a1e0ac167a1db',
'research/ordinary14-74-factor-residues-draft/FactorResidues74.lean':'368e6e5f3db5693db859fdc85a9441f0d6378969563eec289c2c121e6b4b1d60',
'research/ordinary14-74-first-factor-client-draft/FirstFactor74.lean':'fca24f5e8e3be0743e3423f66573e099a211f3c2cfc973d69f77c0a2ff8d62f4',
'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean':'5c441b8df055693e745967f01ef8128d808f5915e3cffb906473499745c4c11b',
'Lean/DiophantineConsistency/ArithmeticAdaptiveScaledNorms2011.lean':'b3b164e528edf0c2b51eecd994140d30389d80b36ae830dccc286dc0e6bf0863',
'Lean/DiophantineConsistency/ArithmeticAdaptiveTransport2011.lean':'e8b22ad05230a0f0815766adcc989caf66251e9bad34eb524da83f9155b5ee24'}
s={}
for p,h in files.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;s[p.rsplit('/',1)[-1]]=b.decode()
a=s['Natural80OwnZeroNorm.lean'];bridge=s['Natural80Partial74.lean'];j=s['Natural80JPos.lean'];u=s['OwnZeroProduct74.lean'];r=s['FactorResidues74.lean'];f=s['FirstFactor74.lean'];g=s['P74PositiveGuard.lean'];norm=s['ArithmeticAdaptiveScaledNorms2011.lean'];trans=s['ArithmeticAdaptiveTransport2011.lean']
def header(src,name):
 m=re.search(r'\btheorem\s+'+name+r'\b(.*?)\s*:=\s*by',src,re.S);assert m,name
 return ' '.join(m.group(1).split())
h=header(a,'units_of_80_zero')
for x in ('(p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)',
 '(hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)',
 '(hb : 0<beta) (hKpos : 0<K)',
 '(hz : InternalZero (P80NaturalForcedGamma.graph p).output v)',
 'let u := partial74 v','u 8*u 8=(m beta u*k u)*(m beta u*k u+k u)+1',
 '(pairEval (P74PositiveGuard.graph p).main u).1=',
 '(pairEval (P74PositiveGuard.graph p).aux u).1=',
 '(pairEval (P74PositiveGuard.graph p).guardFactor u).1=',
 '(pairEval (P74PositiveGuard.graph p).strong u).1='):
 assert x in h,x
assert 'gamma' not in h.lower().replace('p80naturalforcedgamma','') and '(hv :' not in h
for x in ('Natural80JPosDraft.J_pos_of_zero p K v hK hKpos hz',
 '(internalZero_iff_partial p v).mp hz','restricted_residues p u',
 'factor_units_of_zero p beta u hbeta hb hJ hw hs hz74 hm ha hstrong'):
 assert x in a,x
# Partial valuation keeps precisely the target's direct slots, including gamma.
assert 'if j = 0 ∨ j = 3 ∨ j = 8 ∨ j = 11 ∨ j = 12 then v j else v j + 1' in bridge
for i in range(14):
 sample=i*7+3; mapped=sample if i in (0,3,8,11,12) else sample+1
 if i in (0,3,8,11,12):assert mapped==sample
 else:assert mapped==sample+1
assert 'theorem internalZero_iff_partial' in bridge
jh=header(j,'J_pos_of_zero');assert '(hK : (p 1 : DiffRing V) = ι κ) (hκ : 0 < κ)' in jh
fh=header(u,'factor_units_of_zero')
for x in ('(hbeta : (p 0 : DiffRing V)=ι beta) (hb : 0<beta)',
 '(hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)',
 '(hmain :','(haux :','(hstrong :'):
 assert x in fh,x
assert '(hv :' not in fh and 'theorem restricted_residues' in r
assert 'theorem m_at_least_two' in f and '(hb : 0<beta) (hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)' in f
# Main pattern and RHS are syntax-level statements, not assumed graph-norm
# consequences. Check the exact conditional hypotheses and source theorem APIs.
nh=header(a,'main_norm_of_unit')
for x in ('(hunit :','(hroot : Equivalent (pairEval (P74PositiveGuard.graph p).Dstar u) (P,N))',
 '(hrhs : pairEval (mainRhs p) u=(rhs,0))',': magnitude (P,N)*magnitude (P,N)=rhs'):
 assert x in nh,x
assert 'g.U*g.U*(1+((3+4*g.a)+g.a*g.a)*(g.c*g.c))' in a
assert '1+(d*d-u*u*(1+((3+4*a)+a*a)*(c*c)))' in r
assert 'theorem main_shape' in r and 'rw [FactorResidues74Draft.main_shape] at hu' in a
assert 'theorem unit_square_norm' in norm and '(pairEval rhs v).2' in norm
assert 'theorem magnitude_equivalent {p q : Pair V} (h : Equivalent p q)' in trans
assert 'theorem main_norm_of_unit' in a and 'rw [hrhs] at hn' in a and 'rw [hmag] at hn' in a
assert 'Dstar : Expr (Fin 14)' in g and 'U : Expr (Fin 14)' in g and 'a : Expr (Fin 14)' in g and 'c : Expr (Fin 14)' in g
for name in ('units_of_80_zero','main_norm_of_unit'):
 assert '#print axioms DiophantineConsistency.Natural80OwnZeroNormDraft.'+name in a
print(json.dumps({'scope':'bounded source premises and coordinate review; no Lean or graph-derived main norm',
 'pinned_sources':len(files),'direct_slots':[0,3,8,11,12],
 'own_zero_beta_K_representations_and_positivity_explicit':True,
 'gamma_positivity_not_assumed':True,'main_root_and_rhs_bindings_explicit':True,
 'axiom_commands_unexecuted':2},sort_keys=True,indent=2))
