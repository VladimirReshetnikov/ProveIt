#!/usr/bin/env python3
"""Independent exact delta/interface and integer-polynomial checks, no Lean."""
from pathlib import Path
import difflib,hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent;BASE=D/'research/ordinary14-natural79-beta-only-zero-w-draft'
files={
 'old_main':('research/ordinary14-natural79-zero-w-main-norm-draft/Natural79ZeroWMainNorm.lean','afacf4636f4b66e2bff939300347ba5568b72d477a3028ec0a424aba42ce8009'),
 'old_root':('research/ordinary14-natural79-zero-w-root-cut-draft/Natural79ZeroWRootCut.lean','c3fd2660899139ddd335214893e5698a4124399432604111a6aa1942bc8009ec'),
 'old_div':('research/ordinary14-natural79-dvd-reflection-slim-draft/Natural79ZeroWDivisibility.lean.src','4ab36ba289a4cfce93d80bcc6bcb2cc75f0ca2a64d0a729b076846775dac0896'),
 'old_endpoint':('research/ordinary14-natural-forced-w79-ipra-draft/Natural79Endpoint.lean','9b527ff7a8b6e166869f2565b83a8c37956680d538c49557de9c82ea1a6041e6'),
 'jpos':('research/ordinary14-natural79-zero-w-jpos-draft/Natural79ZeroWJPos.lean','f1cf89c29eebe2259069dd26fd66d8cece75d48374358cc95ab9cc1ba83a2f0a'),
 'unit':('research/ordinary14-natural79-factor-residues-draft/Natural79ConcreteUnits.lean','253421a5ac864a94a9926472d9c469c2997d6581cded0aaa3fda27b2830d118d'),
 'shapes':('research/ordinary14-natural79-factor-residues-draft/Natural79ResidueShapes.lean','b4d60c7db8fb92cac53f38f81414a6319d8979ccbcb575d2e29e49fa5a51fd38'),
 'graph':('research/ordinary14-natural-forced-w79-lean-draft/P79NaturalForcedW.lean','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36'),
 'ring':('research/ordinary14-natural79-w-model-route/ForcedWDivisibility.lean','111f5a6da543baf6f08b3b1c6e5e8371cfb222197ba4566b8693598edffb6833'),
 'quotient':('Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean','40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884'),
 'magnitude':('Lean/DiophantineConsistency/Compact44/ReducedNormSigned.lean','c01a13fd7f48c5abeb8a6741e19adad7b9d848fc57d51057c8bbb4694139674c'),
 'author_receipt':('research/ordinary14-natural79-beta-only-zero-w-draft/receipt.json','5331a284de1853e0314c9346c7cc922701a64c99a7328f15b66cbfb7827cba24'),
 'new_main':('research/ordinary14-natural79-beta-only-zero-w-draft/source/Natural79ZeroWMainNorm.lean.src','82d5e0219a93d826b7eff180cfc33c062e1fece7fa18a198208cc787a0a7ee7b'),
 'new_root':('research/ordinary14-natural79-beta-only-zero-w-draft/source/Natural79ZeroWRootCut.lean.src','2be6d79d7cf0bbf86139da63b1120f93509a3dd49ee89a4e221ec6c07ecc7a3d'),
 'new_div':('research/ordinary14-natural79-beta-only-zero-w-draft/source/Natural79ZeroWDivisibility.lean.src','d5240f8385c2a0bd472f25d080c9b4f3312a24ac995dcca51d1a6ac7269acf7f'),
 'new_endpoint':('research/ordinary14-natural79-beta-only-zero-w-draft/source/Natural79Endpoint.lean.src','da1bbfbc339c26ea5763e5ff4c1aaa885898dab9c3fafd21854b8b69e5c54b7b')}
texts={}
for n,(path,h) in files.items():
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==h,n;texts[n]=b.decode()
diffs=''.join(''.join(difflib.unified_diff(texts['old_'+n].splitlines(keepends=True),texts['new_'+n].splitlines(keepends=True),fromfile='old/'+n,tofile='new/'+n,n=3)) for n in ['main','root','div','endpoint'])
if sys.argv==[sys.argv[0],'--emit-diff']:
 sys.stdout.write(diffs);sys.exit(0)
assert sys.argv==[sys.argv[0]] and (P/'exact-deltas.diff').read_text()==diffs
flat=lambda s:re.sub(r'\s+',' ',s)
def head(s,n):
 m=re.search(r'\btheorem '+n+r'\b',s);assert m
 return flat(s[m.start():s.index(':=',m.start())])
main=texts['new_main'];root=texts['new_root'];div=texts['new_div'];ep=texts['new_endpoint']
helper=lambda s:s.split('theorem eval_one_of_pair_unit',1)[1].split('\n\n',1)[0]
assert helper(main)==helper(texts['jpos'])
assert 'import Natural79ConcreteUnits' in main and 'import Natural79ZeroWJPos' not in main
assert 'def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta' in main
cut=lambda s:s.split('  -- BEGIN LITERAL GRAPH\n',1)[1].split('  let g15 :=',1)[0]
assert cut(texts['shapes'])==cut(texts['graph'])
for line in ('let qm := n_J * beta','let q := 1 + qm','let X := q * n_w','let q2 := q * q','let q3 := q * q2','let Y := q3 * s','let U := Y * q2','let E := X * Y','let a := E + Y'):
 assert line in cut(texts['graph']),line
for n,s in [('main_norm_of_zero_w_zero',main),('signed_quotient_of_zero_w_zero',main),('signed_dvd_three_square_of_zero_w_zero',root),('zero_w_impossible',div),('w_pos_of_zero',div)]:
 h=head(s,n);assert '(hbeta : (p 0 : DiffRing V)=ι beta)' in h and '(hK :' not in h and '(hb :' not in h and '(hJ :' not in h,n
assert '(hq : 1≤Q)' in head(div,'no_divisor_in_window') and '(hY : Q*Q*Q≤Y)' in head(div,'no_divisor_in_window')
assert 'have hq : 1≤q beta v := by dsimp [q]; simp' in div
u=head(texts['unit'],'units_of_zero_w_zero');assert '(hz :' in u and '(hw :' in u and '(hbeta' not in u and '(hK' not in u
assert '(hm : 0<m)' in head(texts['quotient'],'scaled_quotient')
assert '(x=ι a ∨ x= -ι a)' in head(texts['magnitude'],'natural_magnitude_square')
assert 'import Natural80Endpoint' in ep and 'import StrictK0Symbolic' in ep
assert 'symbolic_beta_representation' in ep and 'port_one_representation' not in ep and 'symbolic_beta_positive' not in ep
# Independently expand identities in the free commutative integer polynomial ring.
def mon(*xs):return {tuple(sorted(xs)):1}
def add(*args):
 out={}
 for a in args:
  for k,v in a.items():out[k]=out.get(k,0)+v
 return {k:v for k,v in out.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def mul(a,b):
 out={}
 for k,v in a.items():
  for l,w in b.items():
   m=tuple(sorted(k+l));out[m]=out.get(m,0)+v*w
 return {k:v for k,v in out.items() if v}
one=mon();three=add(one,one,one);four=add(three,one)
Y,Q,U,C,H=map(mon,['Y','Q','U','C','H']);q2=mul(Q,Q)
assert add(mul(add(mul(four,Y),three),q2),neg(mul(four,mul(Y,q2))))==mul(three,q2)
# Substitute d² = 1+(Y²+H)C² in U(d²-Y²C²)-UHC².
norm=add(one,mul(add(mul(Y,Y),H),mul(C,C)))
assert add(mul(U,add(norm,neg(mul(mul(Y,Y),mul(C,C))))),neg(mul(mul(U,H),mul(C,C))))==U
assert 3*1*1 < 4*(1**3)*1+3
print(json.dumps({'scope':'independent source-interface, full pinned deltas and free-ring identity checks only; no Lean or model proof',
 'inputs':{n:{'path':p,'sha256':h} for n,(p,h) in sorted(files.items())},
 'complete_unified_diff_sha256':hashlib.sha256(diffs.encode()).hexdigest(),
 'represented_beta_only_at_zero_w_client':True,'copied_unit_lemma_exact':True,
 'retained_endpoint_imports':['Natural80Endpoint','StrictK0Symbolic'],
 'q_equals_one_boundary_checked':True,'axiom_reports_executed':False},indent=2,sort_keys=True))
