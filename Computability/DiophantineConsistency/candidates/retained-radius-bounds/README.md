# Retained-wire quartics with two derived guard signs

The actual first source shift gives t>=1 and n=t+1>=2. Exact combinations
of original raw rows then give2An=T+n^2+1 andD=A^2-1, forcingA>=2 and
D>=3. These implications replace two of the frozen161 private guards.
The original rows and all parents remain unchanged. See `PROOF.md` for
the four ordered shifted bounds and both directions of zero existence.

All variables are unrestricted integers and all equations have exact
degree four:

| Directory | Variables | Rows | Collected terms | Actual height |
|---|---:|---:|---:|---:|
| `retained` | 1,736 | 1,336 | 6,172 | 427 |
| `support2_affine1` | 1,089 | 689 | 5,016 | 4,750 |
| `support2_affine2` | 944 | 544 | 6,780 | 737,653 |
| `support4_affine2` | 880 | 480 | 10,130 | 737,653 |
| `support8_affine2` | 866 | 466 | 10,094 | 938,261 |

From the repository root:

```sh
python3 -B Computability/DiophantineConsistency/tools/build_retained_radius_bounds.py --check
python3 -O -B Computability/DiophantineConsistency/tools/build_retained_radius_bounds.py --check
python3 -B Computability/DiophantineConsistency/candidates/retained-radius-bounds/check.py
python3 -O -B Computability/DiophantineConsistency/candidates/retained-radius-bounds/check.py
```

The checker independently expands the original-row ideal certificates
and strict shifted inequalities before using any macro meaning. It
imports no builder or optimizer. Every guard is preserved through exact
signed restoration. The natural source/refutation calibration is
inherited; no Lean or new internal-ZFC proof is claimed.
