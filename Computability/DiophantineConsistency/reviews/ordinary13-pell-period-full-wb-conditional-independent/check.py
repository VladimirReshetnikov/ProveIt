from pathlib import Path
from hashlib import sha256
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-pell-period-full-wb-conditional-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/ordinary13-pell-period-full-wb-conditional-draft/PellPeriodFullWB.lean.src').read_text()
Q=Path('research/ordinary13-pell-period-bounded-formula-draft/PellPeriodBounded.lean.src').read_text()
G=Path('Lean/DiophantineConsistency/PRAWitnessPR.lean').read_text()
R=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
assert 'theorem wb_exs_bt\'' in G and '(hψ : Hierarchy 𝚺 1 ψ)' in G
assert "ψ.Eval (x :> e) Empty.elim → ∃ x' ≤ A.vval e, ψ.Eval (x' :> e) Empty.elim" in G
assert '(hWB : WB M ψ) : WB M (∃⁰ ψ)' in G
compact=lambda s:re.sub(r'\s+','',s)
inner=re.search(r'def finalBody : ArithmeticSemisentence 8 :=\s*“(.*?)”',P,re.S).group(1)
period=re.search(r'def periodDef : 𝚺₁.Semisentence 2 := \.mkSigma\s*“(.*?)”',Q,re.S).group(1)
innerbody=inner.split('.',1)[1]
assert compact(innerbody)==compact(period.split(',',1)[1])
assert compact(inner.split('.',1)[0])=='tryxhcma'
assert compact(period.split('.',1)[0])=='ma'
assert '∃ c h x y r t,' in period
for label,arity,under in [('R',7,'finalBody'),('Y',6,'bodyR'),('X',5,'bodyY'),('H',4,'bodyX'),('C',3,'bodyH')]:
 assert f'def body{label} : ArithmeticSemisentence {arity} := ∃⁰ {under}' in P
checks={'C':(2,'exp2 (poly ‘2 * (#1 + 2) * #0’) (poly ‘0’)'),
 'H':(3,'poly ‘2 * #1 * #0’'), 'X':(4,'exp2 (poly ‘2 * (#3 + 2) * #0’) (poly ‘0’)'),
 'Y':(5,'exp2 (poly ‘2 * (#4 + 2) * #1’) (poly ‘0’)'),
 'R':(6,'poly ‘#1’'),'T':(7,'poly ‘#1’')}
for label,(arity,rhs) in checks.items():assert f'def bound{label} : BoundTerm {arity} := {rhs}' in P
for label,body in [('C','bodyC'),('H','bodyH'),('X','bodyX'),('Y','bodyY'),('R','bodyR'),('T','finalBody')]:
 assert f'Hierarchy 𝚺 1 {body}' in P and f'Replacement {body} bound{label}' in P
for tok in ["wb_exs_bt' finalBody htS boundT ht (finalBody_wb (M := M))",
 "wb_exs_bt' bodyR hrS boundR hr hT", "wb_exs_bt' bodyY hyS boundY hy hR",
 "wb_exs_bt' bodyX hxS boundX hx hY", "wb_exs_bt' bodyH hhS boundH hh hX",
 "wb_exs_bt' bodyC hcS boundC hc hH", 'change WB M (∃⁰ bodyC)']:
 assert tok in P,tok
assert '“out time b. ∃ state, !runDef state time b ∧ !pi₁Def out state”' in R
assert '“out time b. ∃ state, !runDef state time b ∧ !pi₂Def out state”' in R
# Independent simulated context stack: each new bound witness is prepended.
e=['m','a'];expected={'c':['m','a'],'h':['c','m','a'],'x':['h','c','m','a'],
 'y':['x','h','c','m','a'],'r':['y','x','h','c','m','a'],'t':['r','y','x','h','c','m','a']}
for witness in ('c','h','x','y','r','t'):
 assert e==expected[witness];e=[witness]+e
assert e==['t','r','y','x','h','c','m','a']
assert expected['r'][1]=='x' and expected['t'][1]=='y'
# Degenerate c=0: original r,t can be arbitrarily large, but zero replacement preserves both equations.
for r in (0,1,1000000):
 for t in (0,1,1000000):
  c=0;x=1;y=0
  assert x==1+c*c*r and y==t*c*c
  assert x==1+c*c*0 and y==0*c*c
assert 1000000>1 and 1000000>0
# Positive-c inequalities in bounded arbitrary natural arithmetic, independent of the Pell recurrence.
for c in range(1,8):
 for r in range(8):
  for t in range(8):
   x=1+c*c*r;y=t*c*c
   assert r<=x and t<=y
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'all_six_environment_indices_and_arities_checked':True,'all_six_hierarchy_and_replacement_premises_present':True,
 'wb_exs_order_checked':True,'zero_c_requires_witness_replacement':True,
 'lean_quotation_and_tactics_checked':False,'uniform_witness_code_proved':False,'lean_executed':False},indent=2,sort_keys=True))
