from pathlib import Path
from hashlib import sha256
import json,math,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-pell-blueprint-projection-bounds-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=Path('research/ordinary13-pell-blueprint-wb-draft/PellBlueprintWB.lean.src').read_text()
for t in ['“y x out previous index b. !pi₁Def x previous ∧ !pi₂Def y previous','def FirstBound','def SecondBound','theorem succ_wb_of_bounds']:assert t in s,t
p=(D/'PellBlueprintProjectionBounds.lean.src').read_text()
for t in ['theorem succInner_eval (e : Fin 6 → M)','e 1 = π₁ (e 3) ∧ e 0 = π₂ (e 3)','e 2 = ⟪(e 5+2)*(e 1)+(e 5+1)*(e 5+3)*(e 0)','theorem first_bound','theorem second_bound','succInner_eval (y :> e)','succInner_eval (y :> x :> e)','succ_wb_of_bounds']:assert t in p,t
src=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text();assert '!pairDef out ((b+2)*x+(b+1)*(b+3)*y) (x+(b+2)*y)' in src
f=Path('../../lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Arithmetic/IOpen/Basic.lean').read_text()
for t in ['lemma pi₁_le_self','lemma pi₂_le_self','instance pair_defined','instance pi₁_defined','instance pi₂_defined']:assert t in f,t
# Independent natural controls of all context positions and transition formula.
count=0
for previous in range(150):
 d=math.isqrt(previous);r=previous-d*d
 x,y=(r,d) if r<d else (d,r-d)
 assert x<=previous and y<=previous
 for b in range(5):
  left=(b+2)*x+(b+1)*(b+3)*y;right=x+(b+2)*y
  out=right*right+left if left<right else left*left+left+right
  index=17;e=[y,x,out,previous,index,b]
  assert e[1]==x and e[0]==y and e[2]==out and e[3]==previous and e[5]==b
  outer=[out,previous,index,b];inner=[x]+outer
  assert previous==outer[1]==inner[2]
  count+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'graph_and_source_shapes_checked':True,'natural_context_transition_controls':count,'first_and_second_bounds_only_proposed':True,'lean_executed':False,'iPRA_result':False},sort_keys=True,indent=2))
