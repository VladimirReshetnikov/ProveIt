# Synchronized direct quartics with candidate-output factorial radius

The new local radius `rho=f*n^2` removes two power calls and two shared
exponent groups from the accepted synchronized family. `PROOF.md` proves
both directions for all natural inputs, explicitly allowing an initially
zero proposed factorial output, then checks the global dependency order.
Frozen parents and incoming archives are unchanged. No Lean was run.

| Natural coordinates | Quadratic rows | Degree | Collected terms | Coefficient height |
|---:|---:|---:|---:|---:|
| 502 | 386 | 4 | 20,030 | 83,899,708 |
| 509 | 393 | 4 | 10,592 | 211,184,624 |
| 573 | 457 | 4 | 7,080 | 63,908,810 |
| 850 | 734 | 4 | 4,679 | 63,908,112 |

Each directory supplies the complete residual system and complete
expanded integer polynomial. There are **25** distinct power calls,
**20** exponent groups, **8** bases, **14** binomials and **2** factorials.
Every listed point improves the corresponding old 522/529/596/895 point
in coordinates, rows, terms and height (height is equal at the 509 point).

Regenerate or compare deterministically from the repository root:

```sh
python3 -B Computability/DiophantineConsistency/tools/build_synchronized_factorial_radius.py --check
python3 -O -B Computability/DiophantineConsistency/tools/build_synchronized_factorial_radius.py --check
python3 -B Computability/DiophantineConsistency/candidates/synchronized-factorial-radius/check.py
python3 -O -B Computability/DiophantineConsistency/candidates/synchronized-factorial-radius/check.py
```

The checker imports no contraction optimizer. It authenticates whole
archives and copied sources, independently replays raw affine restoration
and every post-export substitution, verifies 183 literal local scalar
rows and unconditional input licenses, and reconstructs all four SOS
polynomials. Its arithmetic controls include 46,441 factorial candidates,
21 complete factorial witness sets and a rejected unsafe linear radius.
Four deliberately corrupted row/coefficient certificates must fail.

The equation inherits the parent's ordinary numerical-calculus/refutation
argument. This candidate does not establish Con(ZFC), certify global
minimality, or close the separate Lean/internal-ZFC formalization.
