"""Fresh connected-component checks against the already recorded rational data."""
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json

root = Path(__file__).parent / 'evidence'
data = json.loads((root / 'exact.json').read_text())
order = data['checks']['formal_inverse_order']
b = [sum(comb(k, r) * 2**(r*(k-r)) for r in range(k+1))
     for k in range(order+1)]
c = [0]
for k in range(1, order+1):
    c.append(b[k] - sum(comb(k-1, j-1)*c[j]*b[k-j] for j in range(1, k)))
    assert c[k] > 0
    p_top = [v for v in data['P'][k] if v['s'] == k]
    l_top = [v for v in data['L'][k] if v['s'] == k]
    d_top = [v for v in data['D'][k] if v['s'] == k-1]
    assert p_top == [{'s': k, 'h': 0, 't': 0,
                      'coefficient': str(Fraction(b[k], factorial(k)))}]
    assert l_top == [{'s': k, 'h': 0, 't': 0,
                      'coefficient': str(Fraction(c[k], factorial(k)))}]
    assert d_top == [{'s': k-1, 'h': 1, 't': 0,
                      'coefficient': str(Fraction(-c[k], 2*factorial(k)))}]
result = {'checked_orders': order, 'colored_graph_counts': b,
          'connected_colored_graph_counts': c,
          'three_leading_coefficient_identities': True}
with (root / 'connected.json').open('x') as stream:
    json.dump(result, stream, indent=2)
    stream.write('\n')
print(json.dumps(result, sort_keys=True))
