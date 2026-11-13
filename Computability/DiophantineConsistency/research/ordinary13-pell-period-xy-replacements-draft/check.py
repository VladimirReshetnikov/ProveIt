from pathlib import Path
from hashlib import sha256
import json, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D = Path('research/ordinary13-pell-period-xy-replacements-draft')
for p, h in json.loads((D/'pins.json').read_text()).items():
    assert sha256(Path(p).read_bytes()).hexdigest() == h, p
p = Path('research/ordinary13-pell-period-full-wb-conditional-draft/PellPeriodFullWB.lean.src').read_text()
for t in ['def bodyR : ArithmeticSemisentence 7 := ∃⁰ finalBody', 'def bodyY : ArithmeticSemisentence 6 := ∃⁰ bodyR', 'def bodyX : ArithmeticSemisentence 5 := ∃⁰ bodyY', 'def boundX : BoundTerm 4 := exp2 (poly ‘2 * (#3 + 2) * #0’) (poly ‘0’)', 'def boundY : BoundTerm 5 := exp2 (poly ‘2 * (#4 + 2) * #1’) (poly ‘0’)']:
    assert t in p, t
p = Path('research/ordinary13-pell-period-final-replacements-draft/PellPeriodFinalReplacements.lean.src').read_text()
for t in ['def BodyData (t r y x h c m a : V)', 'xDef.val.Evalb ![x,h,a] ∧ yDef.val.Evalb ![y,h,a]', 'def BodyEvaluationBridge : Prop']:
    assert t in p, t
s = (D/'PellPeriodXYReplacements.lean.src').read_text()
for t in ['Replacement bodyX boundX', 'Replacement bodyY boundY', 't :> r :> y :> x :> e', 't :> r :> y :> e', 'BodyData t r y x (e 0) (e 1) (e 2) (e 3)', 'BodyData t r y (e 0) (e 1) (e 2) (e 3) (e 4)', 'x_defined.defined ![x,e 0,e 3]', 'y_defined.defined ![y,e 1,e 4]', 'hg.mp data.2.2.1', 'hg.mp data.2.2.2.1', '⟨x, ?_, original⟩', '⟨y, ?_, original⟩']:
    assert t in s, t
assert ['t','r','y','x'] + ['h','c','m','a'] == ['t','r','y','x','h','c','m','a']
assert ['t','r','y'] + ['x','h','c','m','a'] == ['t','r','y','x','h','c','m','a']
count = 0
for a in range(7):
    x, y = 1, 0
    for h in range(9):
        bound = 2**(2*(a+2)*h)
        assert x <= (2*(a+2))**h <= bound
        assert y <= (2*(a+2))**h <= bound
        x, y = (a+2)*x+(a+1)*(a+3)*y, x+(a+2)*y
        count += 1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(), 'body_and_bound_source_shapes_checked':True, 'x_outer_environment':['h','c','m','a'], 'y_outer_environment':['x','h','c','m','a'], 'x_inner_witnesses':['y','r','t'], 'y_inner_witnesses':['r','t'], 'finite_pair_controls':count, 'quotation_and_boundterm_elaborated':False, 'lean_executed':False}, sort_keys=True, indent=2))
