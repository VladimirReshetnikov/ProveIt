# Nine-positive saturated Pell constructions

`section.tex` gives the integrated ordinary proof; the three expanded audit notes in `certificates/` give additional detail. There are exactly nine strictly positive variables: `b,g,h,s,w,C,i,j,n`.

| Equation | Degree | Live binary operations | Coherent native tuple |
|---|---:|---:|---|
| `equations/compact2082_simple.json` | 1,628,768 | 435 | compact54-sharp |
| `equations/h1868_simple.json` | 1,474,688 | 449 | original31 |
| `equations/h1868_complete.json` | 999,518 | 1,086 | original31 |

Each JSON is a complete division-free straight-line polynomial. Its fixed leaves are materialized under `baseline/compact2082/fixed/` or `fixed/h1868/`, with sign and raw/gzip SHA-256 bindings. The native tuples are also retained, with original31's finite generation recipe under `native_original31/`. Their exact equality to the active data was checked when the release was assembled.

The positive H1868 source has radix `B=2^2134939 b^2`, block scale `L=2 b B^1986`, and threshold `N=2^16012032 B^1055`. The factor 2 and absence of an extra b in N matter. Its 31 weights and 22 targets are in `data/code.json`; the full source residuals and extraction kernels are in `data/source.json` and `data/kernels.json`.

The 333-term integer polynomial in `data/saturated_corrected_P.json` is the complete-radical majorant. `verify_majorant.py` reconstructs its exact formal square-root recurrence and correction. The uncorrected approximation is deliberately retained as a negative control: it is not a valid uniform upper bound. The corrected defect, translated by `(A,C,i,Z)=(x+3,y+1,u+1,v+1)`, is exactly the 36,309-term positive polynomial in `data/saturated_corrected_certificate.json`.

Run from any working directory with Python 3.10+:

```sh
python3 nine/verify.py
python3 nine/certificates/audit_h1868_degree.py
python3 nine/certificates/check_saturation.py
```

The second script is an independent exact implementation and does not import the circuit producer. The first script also regenerates the literal circuit and checks independent modular formula evaluations. Their roles and the unbounded ordinary proof boundary are kept distinct. `build.py` deterministically reproduces all three circuits.

`baseline/` and `native_original31/` preserve inherited mathematical and data provenance. They are not additional automatic commands in the release verifier. The root `PROOF_STATUS.md` explains the inherited native/compiler and logical-calibration dependency.
