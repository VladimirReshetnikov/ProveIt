# Signed horizons composed with a reused CRT anchor and oriented powers

All eight equations here have unrestricted integer variables. Their ordinary
mathematical equivalence to syntactic Con(ZFC) composes the new proof in
`proofs/COMPOSITION_PROOF.md` with the explicitly inherited C222/ZF/ZFC
calibration. No new complete Lean/Rocq build or encoded ZFC proof is claimed.

The source has no K215 machine simulation or Jones universal polynomial.
Each final JSON is a complete finite straight-line polynomial circuit using
only integer constants, addition, subtraction, and multiplication. Registers
are abbreviations, not additional variables. The polynomial is a sum of
squares of the listed residual polynomial registers.

| Integer variables | Exact degree | Squared residuals | Binary operations | Largest literal constant |
|---:|---:|---:|---:|---:|
| 131 | 12 | 70 | 2475 | 1099511627780 |
| 132 | 12 | 71 | 2484 | 256 |
| 117 | 16 | 56 | 2439 | 256 |
| 108 | 32 | 47 | 2434 | 256 |
| 97 | 128 | 36 | 2418 | 256 |
| 91 | 256 | 30 | 2400 | 256 |
| 87 | 32768 | 26 | 2388 | 256 |
| 86 | 2097780 | 25 | 2385 | 256 |

A literal constant is distinct from a coefficient of the fully expanded
polynomial. `METRICS.json` reports proved strict power-of-two bounds on every
expanded coefficient, and matched earlier Oriented Powers profiles. No exact
expanded height is substituted for those upper bounds.

The new semantic step removes a square horizon guard without losing its
positive branch: the 219-source uses a signed affine exponent to recover the
sign, while the 221-source uses the beta endpoint divisor and a retained
q^t request. The CRT identity `B*u=C+F+1` recovers B != 0 by parity, enabling
oriented pooling after the old factorial bootstrap was removed. The complete
argument, zero-base cases, and ordering of all sign deductions are included.

From this directory, with Python 3.10 or later and only its standard library:

```sh
python3 -B verify.py
python3 -O -B verify.py
python3 -B build.py --output /tmp/signed-horizon-rebuilt
python3 -B evaluate.py --profile integer108_degree32_staged --variables
python3 -B evaluate.py --profile integer108_degree32_staged --zero --modulus 1000000007
```

`verify.py` checks every literal source binding, all acyclic unit pivots,
local circuit expansions, degree certificates, coefficient bounds, and
nonzero derivative witnesses for actual occurrence of every quantified
coordinate. It rejects deliberately corrupted domains, gates, pivots, degrees,
and pool selections. `build.py` writes a fresh reconstruction and compares its
bytes with every frozen equation. Neither program searches for a zero.

`SOURCE_PINS.json` authenticates the repository inputs at commit
`02a78a08603cbae248c19c23a75907c6c6bd6443` and identifies the earlier Oriented
Powers archive. Original notices and the repository license are retained.
This packet does not bundle the complete historical Lean dependency closure.
