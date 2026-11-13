from pathlib import Path
from hashlib import sha256
import json,math,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-pell-blueprint-wb-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
for t in ['“out b. !pairDef out 1 0”','“out previous index b. ∃ x y,','!pi₁Def x previous ∧ !pi₂Def y previous ∧','!pairDef out ((b+2)*x+(b+1)*(b+3)*y) (x+(b+2)*y)”','zero := zeroDef','succ := succDef']:assert t in s,t
a=Path('Lean/DiophantineConsistency/PRAWitnessArithmetic.lean').read_text()
for t in ['theorem wb_pairDef','theorem wb_pi₁Def','theorem wb_pi₂Def']:assert t in a
b=Path('Lean/DiophantineConsistency/PRAWitnessCalculus.lean').read_text()
for t in ['theorem wb_exs_term','(hb : ∀ (e : Fin n → M) (y : M)','macro "wb_auto" : tactic']:assert t in b
f=Path('../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic/IOpen/Basic.lean').read_text()
for t in ['lemma pi₁_le_self','lemma pi₂_le_self','instance pi₁_defined','instance pi₂_defined']:assert t in f
p=(D/'PellBlueprintWB.lean.src').read_text()
for t in ['theorem zero_wb','theorem first_projection_bound','theorem second_projection_bound','theorem succInner_wb','def FirstBound','def SecondBound','wb_exs_term ‘#1’','wb_exs_term ‘#2’','change WB M (∃⁰ (∃⁰ succInner))']:assert t in p
# Source context controls: after binding x, e=[out,previous,index,b];
# after binding y, e=[x,out,previous,index,b].
outer=['out','previous','index','b'];inner=['x']+outer
assert outer[1]==inner[2]=='previous'
for value in range(10000):
 n=math.isqrt(value);d=value-n*n
 x,y=(d,n) if d<n else (n,d-n)
 pair=y*y+x if x<y else x*x+x+y
 assert pair==value and x<=value and y<=value
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'zero_and_successor_source_shapes_checked':True,'outer_previous_index':1,'inner_previous_index':2,'standard_projection_controls':10000,'projection_formula_extraction_proved':False,'successor_quote_definitional_equality_checked_by_lean':False,'lean_executed':False},sort_keys=True,indent=2))
