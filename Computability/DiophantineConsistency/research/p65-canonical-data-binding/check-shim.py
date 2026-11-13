#!/usr/bin/env python3
"""Check that the arithmetic shim changes exactly the listed imports."""
from hashlib import sha256
from pathlib import Path
import sys

if sys.flags.optimize:
    raise SystemExit('Run without Python optimization')
root = Path(__file__).resolve().parents[2]
source = root / 'Lean/DiophantineConsistency/Compact44/P72ConvArith.lean'
shim = Path(__file__).with_name('P72ConvArithShim.lean')
old = ('import DiophantineConsistency.Compact44.P72Facts\n'
       'import DiophantineConsistency.ArithmeticRepunit\n'
       'import DiophantineConsistency.Compact44.ArithmeticControllerChoiceCompact44Triangle')
new = ('import FreeJHaltModelZero\n'
       'import DiophantineConsistency.ArithmeticRepunit\n'
       'import DiophantineConsistency.ArithmeticStandardCasts\n'
       'import DiophantineConsistency.ArithmeticControllerChoiceCompact44Triangle')
a = source.read_text()
b = shim.read_text()
assert sha256(a.encode()).hexdigest() == '8427fda2445abaa8b87ae09ce8b99f4c2d5e332e5e14b7cb8b78c66c8dacbb75'
assert sha256(b.encode()).hexdigest() == 'b80e2933eb70db9341898a8cb7cc44be7296d78892dbcb5e72362bcc5346e890'
assert a.count(old) == 1 and a.replace(old, new, 1) == b
print('P72ConvArith shim differs only in the recorded imports')
