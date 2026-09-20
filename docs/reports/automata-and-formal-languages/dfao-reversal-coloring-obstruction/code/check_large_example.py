#!/usr/bin/env python3
"""Independent tuple-set BFS for the corrected n=8,k=5 example."""
import json
from pathlib import Path
from reversal import orbit, u_witness


def main():
    p, s, tau = u_witness(3, 5, 5)
    reached = orbit(tau, (p, s))
    total = xor_value = 0
    for c in reached:
        encoded = sum(c[i] * 5 ** i for i in range(8))
        total += encoded
        xor_value ^= encoded
    assert (len(reached), total, xor_value) == (369020, 72076669650, 128342)
    result = {'n': 8, 'k': 5, 'orbit': len(reached),
              'orbit_sum': total, 'orbit_xor': xor_value,
              'method': 'Python tuple-set BFS, independently compared with C++ integer-state BFS'}
    out = Path(__file__).resolve().parents[1] / 'data/independent_python_bfs.json'
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
