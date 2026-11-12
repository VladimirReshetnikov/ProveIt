#!/usr/bin/env python3
"""Static independent residual, cancellation and endpoint-source review."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
base='research/adaptive-aq34-natural172-lean-bridge-draft/'
l=pin(base+'AQ34Natural172Literal.lean.src','db139aa6e449b5a5f07f4097fd8dd750cd35af2e87bc1ca76655bba430ae5a10')
r=pin(base+'AQ34Natural172Residuals.lean.src','ff2b653db9b276bba9c76f0ebdfd9ed9f81dba5d9ca4af5e46a64bf91e0760f6')
b=pin(base+'AQ34Natural172Bridge.lean.src','70664b7357a4353c6cc33f6583336a533f9bf1f4e04651ec1b0d68a3b1200adb')
pin(base+'result.json','64fa83dc5e938dc73df4452d34dfc4656ec774a08522c40c06503f447bad686e')
pin(base+'source-result.json','e378586bc05bc525440d33773b229e92226e7884903f9fd2d2d794856e90880b')
pin('reviews/adaptive-aq34-natural172-independent/result.json','bc389ee09321ae64ec9fdbe3e51ecc4c3f90dd65323748ffb247ca8b7e7a88d2')
p=json.loads(pin('research/adaptive-square-sums34/candidate.json','9c7fdcf0289b0407af4bbb9deaef4d52fd37435c162a8d15199d1ec9902e1f77'))
c=json.loads(pin('research/adaptive-aq34-natural172-signed-cancel/candidate.json','2bc8d1be1d3e4ca72dd84255816bda819bd75423447c6799c3aa52b8583d8f23'))
ctx=pin('Lean/DiophantineConsistency/AdaptiveAQ34Context.lean','2f581a4dcd732d0f4b5f1c2f39a183dba00d5f7cca37c725009dd505f98291cd')
old=pin('Lean/DiophantineConsistency/AdaptiveAQ34Literal.lean','30e3a0e4bc8199bcb62d27bcc0cc6a73697027f9c0066d24cbaad340eb2df38b')
ep=pin('Lean/DiophantineConsistency/IPRAAQ34Native.lean','857f4eb24f59efabfb49b9e6ba038bc43d1ffd81af70b21827f4b68153f5a31d')
for s in (l,r):
 for i,n in enumerate(c['witnesses']):assert f'let {n} : Expr (Fin 34) := .var {i}' in s
 for i,n in enumerate(c['fixed_numerals']):assert f'let {n} : Expr (Fin 34) := .constant (p {i})' in s
 for n,op,x,y in c['source']:assert f'  let {n} := {x} {op} {y}\n' in s,n
assert len(c['source'])==172 and len(p['source'])==144
for label,i,j in [('w',18,19),('d',23,24),('v',25,26)]:
 theorem=re.search(r'(?ms)^theorem '+label+r'_cancel\b(.*?)(?=^theorem )',b).group(1)
 assert f'(v {i}+1)-(v {j}+1)=v {i}-v {j}' in theorem
assert [p['witnesses'][i] for i in (18,19,23,24,25,26)]==['wPositive','wNegative','dPositive','dNegative','vPositive','vNegative']
for name,left,right in [('namedBt','wPositive','wNegative'),('Dstar','dPositive','dNegative'),('V','vPositive','vNegative')]:
 assert [name,'-',left,right] in p['source'] and [name,'-','n_'+left,'n_'+right] in c['source']
 assert [row[0] for row in p['source'] if left in row[2:]]==[name] and [row[0] for row in p['source'] if right in row[2:]]==[name]
def vec(s):
 v=re.findall(r'^  !\[([^\n]+)\]$',s,re.M);assert len(v)==1;return v[0].split(',')
cv=vec(r);pv=vec(ctx);assert len(cv)==22 and cv==pv
for i,name in enumerate(cv):
 q=re.search(r'(?ms)^theorem residual%02d\b(.*?)(?=^theorem )'%i,b);assert q
 q=q.group(1)
 for x in [f'AQ34Natural172ResidualsDraft.residuals p {i})',f'AdaptiveAQ34Context.residuals p {i})','AdaptiveAQ34Context.newFill k','fun i => v i+1','[CommRing R]']:assert x in q,(i,x)
 assert f'h{i:02d} := residual{i:02d} p v' in b
# Both sums carry exactly the same left-associated ordered list of squared residuals.
sumstr=' + '.join(f'(residuals p {i})*(residuals p {i})' for i in range(22))
assert f'def sum (p : Fin 4 → ℤ) : Expr (Fin 34) := {sumstr}' in r
assert f'def sum (p : Fin 4 → ℤ) : Expr (Fin 2 ⊕ Fin 32) := {sumstr}' in ctx
assert 'theorem sum_eq_literal (p : Fin 4 → ℤ) : sum p = AQ34Natural172LiteralDraft.literal p := by rfl' in r
assert '(sum p).subst newFill = literal p := by rfl' in old
for x in ['rw [positiveShift, ModelJonesSyntax.evalRing_subst]','← AdaptiveAQ34Literal.new_literal, ModelJonesSyntax.evalRing_subst','← AQ34Natural172ResidualsDraft.sum_eq_literal','∀ (R : Type) [CommRing R] (p : Fin 4 → ℤ) (v : Fin 34 → R)','IPRAAQ34Native.bridge34','theorem native_equivalence (h : EvaluationIdentity)','theorem standard_equivalence (h : EvaluationIdentity)','theorem reference_equivalence (h : EvaluationIdentity)']:assert x in b,x
assert 'positiveShift\n  (AdaptiveAQ34Literal.literal CurrentWindowCarry2011.ports)' in ep and '∼mappedNativeRefutation embedding' in ep
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',l+r+b)
print(json.dumps({'scope':'source-only review, no Lean elaboration, axiom report or provider authentication','literal_and_residual_source_rows':172,'common_residual_signatures':22,'ordered_squares':22,'signed_shift_cancellations':3,'endpoint_evaluation_identity_premise_explicit':True,'parent_fixed_port_target_verified':True},sort_keys=True,indent=2))
