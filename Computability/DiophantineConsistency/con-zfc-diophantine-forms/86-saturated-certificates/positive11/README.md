# Strong-Pell budget companion

One explicit fixed integer polynomial in **11 strictly positive unknowns**,
of **exact degree 213**, using **112 live binary arithmetic operations**.
Its positive unsolvability is equivalent to Con(ZFC), by the ordinary
proof in `PROOF.md` composed with the named inherited compact44 native
source calibration. This is not a newly compiled formal certificate.

The input variables are `j,F,alpha,i,T,X,Y,n,eta,zeta,gamma`. The literal
division-free polynomial is `p11_positive_degree213.json`; the four fixed
numerals are bound to actual compressed payloads in `coefficients/`.

The new idea is to prove that an already available strong-Pell witness
`i` dominates the needed transport bounds, then center the octic norm at
both `V` and `(a+2)I`. This replaces the incoming degree-257/114-operation
centered equation by degree 213/112 operations. The incoming 277/111
equation remains a lower-operation-count alternative.

Run from this folder:

```sh
python3 build.py
python3 verify.py
python3 -O verify.py
```

Only Python's standard library is required. The checker independently
expands the prefix formulas, the octic norm, and its double-centered
leading form; validates the selected nonzero degree-213 coefficient;
checks every payload hash, variable and gate count, and deterministic
rebuild; and checks small constructed Pell examples. All assertions
used for validation remain active under `python -O`.

The new unbounded argument is in `PROOF.md`, Sections 4--6. Finite checks
do not prove consistency or substitute for the inherited source theorem.
The retained incoming proofs and input digests under `provenance/` make
the exact semantic dependencies inspectable.

The arithmetic DAG framework and exact sparse ring are adapted from the
incoming `ZFC_Diophantine_Joint_Guards` packet at ProveIt commit
`c1a102936aca437e9999530a0111e6ddab56dc6d`; that packet builds on sources
61, 65, and 70. Fixed numerals are copied unchanged as one coherent
compact44 tuple. See `NOTICE.md` and the inherited notices for provenance.
