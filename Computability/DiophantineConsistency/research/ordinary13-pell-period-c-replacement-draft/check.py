from pathlib import Path
from hashlib import sha256
import json, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D = Path('research/ordinary13-pell-period-c-replacement-draft')
for p, h in json.loads((D/'pins.json').read_text()).items():
    assert sha256(Path(p).read_bytes()).hexdigest() == h, p
prior = Path('research/ordinary13-pell-period-full-wb-conditional-draft/PellPeriodFullWB.lean.src').read_text()
for t in ['def bodyR : ArithmeticSemisentence 7 := ∃⁰ finalBody', 'def bodyY : ArithmeticSemisentence 6 := ∃⁰ bodyR', 'def bodyX : ArithmeticSemisentence 5 := ∃⁰ bodyY', 'def bodyH : ArithmeticSemisentence 4 := ∃⁰ bodyX', 'def bodyC : ArithmeticSemisentence 3 := ∃⁰ bodyH', 'def boundC : BoundTerm 2 := exp2 (poly ‘2 * (#1 + 2) * #0’) (poly ‘0’)']:
    assert t in prior, t
r = Path('research/ordinary13-pell-period-final-replacements-draft/PellPeriodFinalReplacements.lean.src').read_text()
for t in ['def BodyData (t r y x h c m a : V)', 'yDef.val.Evalb ![c,m,a] ∧ h=2*m*c', 'def BodyEvaluationBridge : Prop']:
    assert t in r, t
s = (D/'PellPeriodCReplacement.lean.src').read_text()
for t in ['theorem cReplacement (evalBody : BodyEvaluationBridge) : Replacement bodyC boundC', 't :> r :> y :> x :> h :> c :> e', 'BodyData t r y x h c (e 0) (e 1)', 'y_defined.defined ![c,e 0,e 1]', '⟨c, ?_, original⟩', 'cReplacement bodyEvaluationBridge']:
    assert t in s, t
assert ['t','r','y','x','h','c','m','a'] == ['t','r','y','x','h','c'] + ['m','a']
controls = 0
for a in range(7):
    x, y = 1, 0
    for m in range(9):
        assert y <= (2*(a+2))**m <= 2**(2*(a+2)*m)
        x, y = (a+2)*x+(a+1)*(a+3)*y, x+(a+2)*y
        controls += 1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(), 'body_and_bound_source_shapes_checked':True, 'outer_environment':['m','a'], 'nested_witness_order':['h','x','y','r','t'], 'finite_pell_controls':controls, 'quotation_and_boundterm_elaborated':False, 'lean_executed':False}, sort_keys=True, indent=2))
