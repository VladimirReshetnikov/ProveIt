# A quartic in 212 unrestricted integers

Start with `report.pdf`; `PROOF.md` contains the complete new ordinary argument.

| Endpoint | Variables | Quadratic rows | Degree | Terms | Coefficient height |
|---|---:|---:|---:|---:|---:|
| New scaled-dyadic equation | **212** | **151** | **4** | **5,357** | **17,592,186,044,420** |
| Credited source173 companion | 213 | 152 | 4 | 5,402 | 2,417,851,639,242,452,488,945,685 |

The new equation strictly improves variables, rows, support and height against
that companion while retaining degree four.
The round22 215-variable equation still has much smaller coefficients; no
claim of global minimality or proof of consistency is made.

The key change scales the growth Pell pair by D=2^20, proves orientation using
integer doubling identities rather than invalid modular cancellation, and
weakens its cap just enough to avoid squared-D coefficients. The affine even
base d=4t+2 eliminates the private cofinal-horizon coordinate. Signed bootstrap,
t=0 exclusion, and the t=1 constructor-bound repair are proved explicitly.

`integer212/equation.json` is the full residual system;
`expanded_polynomial.json` lists every collected quartic coefficient.
The `base213` file is only a marked staging array with inactive row130 and
coordinate184. It is not a competing endpoint.

Offline Python 3, standard library only:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --parent
python3 -B -O verify.py --parent
python3 -B build.py --out /tmp/rebuilt212
```

Checks are read-only except when an explicit `--receipt` or `--out` is supplied.
Every normal verification rebuilds from a fresh relocated copy. The optional
parent check runs the complete original source173 release, whose exact ZIP
bytes and immediate pre-optimization stage are authenticated. New certificates
use only relative paths. Exact maps, all literal coefficients, an independent
checker, editable LaTeX and the full original ordinary-proof source closure
are included. No network, root search or fresh Lean/Rocq build is involved.
