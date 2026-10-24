# Eleven positive unknowns, degree 277

This component improves package 70's degree-325/113-operation polynomial
to degree 277 and 111 operations. It uses the universal rational Pell
integrality lemma from package 69 to delete `q(q-1)` from the strong Pell
ordinate. See `PROOF.md` for the complete new equivalence argument and its
inherited native/K215 boundary.

Run:

```sh
python3 build.py
python3 verify.py
python3 -O verify.py
```

The literal polynomial is `p11_positive_degree277.json`; four coherent
fixed integer payloads are included under `coefficients/`. The circuit
uses eleven strictly positive unknowns. Derived registers are polynomial
abbreviations, not quantified variables. `audit.py` performs exact sparse
polynomial checks using a helper adapted from package 70.

No global optimum, reduction below nine positive unknowns, new end-to-end
kernel certificate, or independent consistency result is claimed.
