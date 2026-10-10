#!/usr/bin/env python3
"""Record a version-specific polylog order-derivative diagnostic.

A discrepancy is a numerical observation, not an analytic counterexample.
The exact root-of-unity reduction supplies the reference representation.
Future versions may eliminate the discrepancy; this script does not require it.
"""
from __future__ import annotations
import json, platform
from pathlib import Path
import mpmath as mp


def main() -> None:
    mp.mp.dps = 40
    z = mp.mpc(0, 1)
    direct = lambda s: mp.re(mp.polylog(s, z))
    reduced = lambda s: mp.power(2, -s) * (mp.power(2, 1-s)-1) * mp.zeta(s)
    rows = []
    for order in (0, 1, 2):
        d = mp.diff(direct, 2, order)
        r = mp.diff(reduced, 2, order)
        rows.append({'derivative_order': order, 'direct': mp.nstr(d, 40),
                     'root_of_unity_reduction': mp.nstr(r, 40),
                     'absolute_discrepancy': mp.nstr(abs(d-r), 12)})
    data = {'status': 'RECORDED', 'python': platform.python_version(),
            'mpmath': mp.__version__, 'dps': mp.mp.dps,
            'argument': 'exact mpc(0,1)', 'spectral_point': 2,
            'method': 'mp.diff defaults; no extra precision or Cauchy method',
            'interpretation': 'Version-specific diagnostic, not a failure of the mathematical identity. Use exact cyclotomic reduction for this check.',
            'checks': rows}
    path = Path(__file__).resolve().parents[1] / 'results' / 'polylog_derivative_canary.json'
    path.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps(data, indent=2))


if __name__ == '__main__':
    main()
