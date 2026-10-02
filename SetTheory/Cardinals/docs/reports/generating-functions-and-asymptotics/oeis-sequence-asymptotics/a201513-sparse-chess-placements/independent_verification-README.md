# Independent verification

These checks use a different row-mask dynamic program and a different symbolic coefficient extraction from the connected-support producer.

- `row_dp.cpp` computes truncated finite-board independence polynomials using row masks (one preceding row for kings, two for knights)
- `row_dp_counts.txt` contains its frozen outputs
- `check_coefficients.py` checks the exact cluster polynomials against those outputs at all board sizes satisfying the proved polynomial threshold (111 comparisons), then obtains the asymptotic coefficients independently using Touchard moments and finite exact interpolation of falling-factorial coefficient polynomials
- `check_results.json` is the exact frozen result

Run `python independent_verification/check_coefficients.py` from the package root (SymPy 1.14.0).

To recreate the finite-board data, compile `row_dp.cpp` with a C++17 compiler, then run it with arguments `king n K` or `knight n K`, where n is board side and K is the truncation order. The supplied outputs use boards n≤13 and K≤8. The implementation uses uint64_t, a fixed coefficient buffer of length 13, and bit masks; it is a finite verification program, not an arbitrary-size counting API. Do not use unsupported arguments or parameters for which counts overflow uint64_t.

## Full row-DP regeneration

This is separate from `replay.sh`, which uses the frozen row-DP output. A complete independent regeneration can be checked without modifying that baseline:

```sh
g++ -O2 -std=c++17 independent_verification/row_dp.cpp -o /tmp/chess_row_dp
python - <<'PYCODE'
from pathlib import Path
import subprocess
p = Path('independent_verification/row_dp_counts.txt')
actual = []
for line in p.read_text().splitlines():
    fields = line.split()
    piece, n = fields[:2]
    K = len(fields) - 3
    actual.append(subprocess.check_output(
        ['/tmp/chess_row_dp', piece, n, str(K)], text=True).strip())
assert '\n'.join(actual) + '\n' == p.read_text()
print('Full row-DP regeneration matches the frozen output exactly')
PYCODE
```

Run from the package root. This extra check is substantially more expensive than verifying the stored exact results.
