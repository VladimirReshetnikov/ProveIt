"""Compare exact data exactly and numerical strings to an explicit tolerance."""
import json, sys
from pathlib import Path
from decimal import Decimal, InvalidOperation, localcontext
expected, actual = map(Path, sys.argv[1:])
files = ['coefficients.json','numeric-checks.json','fixed-range-checks.json',
         'checks.json','sector-checks.json','stabilization-checks.json']
comparisons = 0

def compare(x, y, path):
    global comparisons
    if type(x) != type(y):
        raise AssertionError(f'{path}: types differ')
    if isinstance(x, dict):
        assert x.keys() == y.keys(), path
        for k in x: compare(x[k],y[k],f'{path}/{k}')
    elif isinstance(x, list):
        assert len(x) == len(y), path
        for i,(a,b) in enumerate(zip(x,y)): compare(a,b,f'{path}/{i}')
    elif isinstance(x, str):
        try:
            a,b = Decimal(x),Decimal(y)
        except InvalidOperation:
            assert x == y, path
        else:
            assert a.is_finite() and b.is_finite(), path
            # Exact rational/integer fields stay exact. Decimal numerical
            # strings use a 40-digit relative-or-absolute tolerance.
            if '.' not in x and 'e' not in x.lower(): assert a == b, path
            else:
                with localcontext() as ctx:
                    ctx.prec=100
                    assert abs(a-b) <= Decimal('1e-40')*max(Decimal(1),abs(a)), path
        comparisons += 1
    else:
        assert x == y, path
        comparisons += 1
for name in files:
    compare(json.loads((expected/name).read_text()),json.loads((actual/name).read_text()),name)
print(f'PASS: {len(files)} result files, {comparisons} scalar checks; numerical tolerance 1e-40')
