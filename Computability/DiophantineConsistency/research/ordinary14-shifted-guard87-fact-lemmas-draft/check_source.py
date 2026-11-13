#!/usr/bin/env python3
"""Low-disk source-only inventory; not a Lean or proof check."""
from pathlib import Path
import hashlib, json, re
root = Path(__file__).resolve().parents[2]
here = Path(__file__).resolve().parent
sources = [here / 'ShiftedGuardFacts.lean'] + [root / 'Lean/DiophantineConsistency' / (n + '.lean') for n in (
    'ArithmeticAdaptiveQuotients2011', 'ArithmeticAdaptiveMainOrientation2011',
    'ArithmeticAdaptiveFactorThree2011', 'ArithmeticAdaptiveRankCongruence2011',
    'ArithmeticAdaptiveFirstDivisibility2011', 'ArithmeticSignedPairs',
    'ArithmeticSquareDivisibility')]
s = sources[0].read_text()
for name in ('oriented_scaled_pair', 'sign_free_main_quotient', 'q4_rank_from_balance'):
    assert re.search(r'\btheorem\s+' + name + r'\b', s)
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', re.sub(r'#print axioms.*', '', s))
assert 'hrad : 0<radicand' in s and 'hY : q^3∣Y' in s and 'hbalance :' in s
print(json.dumps({'scope':'source inventory only; no Lean invocation', 'sha256':{str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}}, indent=2, sort_keys=True))
