# Further logical frontends and reproducible proof certificates

This directory records mathematical alternatives explored while building
the merged-G candidate. Their logical calibrations and their compiled
costs are separate questions. The main candidate uses the exact native
deductive equivalence proved for the merged Euclidean/helper row. The
alternatives here are retained for future compiler and encoding searches;
they are not claims of global minimality or separate improved machines.

## Reproduce every exploratory certificate

With Python 3.9 or later, run:

```
python research_reproduce.py --output-dir reproduced
```

Only these six scripts need be present next to one another:

* `research_reproduce.py`
* `combined_helper_certificate.py`
* `crossed_box_helper_certificate.py`
* `specialization_crossed_helper_certificate.py`
* `gated_crossed_helper_certificate.py`
* `canonical_crossed_helper_certificate.py`

No retained proof JSON, receipt JSON, upstream checkout, network access,
third-party package, or proof assistant is used as an input. The driver
copies the five certificate scripts into the chosen output directory and
runs all nine modes in fresh Python processes. Each certificate generates
its full proof JSON, checks every proof node, reloads it, and checks again.
The driver checks the resulting proof SHA256 against an embedded retained
hash and writes `research_reproduction_receipt.json`. The large proof JSON
files can therefore be omitted from the distribution archive.

## Modes and uniform mathematical arguments

| Mode | Formula change | Uniform argument | Status |
|---|---|---|---|
| `combined` | `e -> All_k(e and reverse(e))` | `combined_helper_calibration.md` | Interderives the ordinary helper and primitive symmetry. |
| `c2_rel` | `e -> All_k All_k reverse(e)`, native Rel binder | `crossed_box_helper_calibration.md` | Complete membership-defined equality interpretation. |
| `c2_sum` | Same, with `k=a+b+1` | Same file | Same interpretation with a cheaper fresh arithmetic binder. |
| `specialization_c1` | General `All_i A -> A` plus full gated crossed helper | `specialization_crossed_helper_calibration.md` | Derives primitive symmetry and every full gated Eq-vacuity instance. |
| `gated_c1` | Full gated `Eq(a,b) -> All_c Eq(b,a)`, with rho7 omitted | `single_crossed_helper_calibration.md` | Complete equality interpretation without primitive symmetry. |
| `canonical_rel` | Canonical crossed helper at `RelCode(a,b)` | Same file | Complete equality interpretation with explicit collision guards. |
| `canonical_reverse_rel` | Canonical crossed helper at `RelCode(b,a)` | Same file | Same proof, reversed native binder orientation. |
| `canonical_affine_a` | Canonical crossed helper at `2a+b+1` | Same file | Same proof with asymmetric affine binder. |
| `canonical_affine_b` | Canonical crossed helper at `a+2b+1` | Same file | Same proof with the other affine orientation. |

The individual commands, useful during source experimentation, are:

```
python combined_helper_certificate.py
python crossed_box_helper_certificate.py --kappa rel
python crossed_box_helper_certificate.py --kappa sum
python specialization_crossed_helper_certificate.py
python gated_crossed_helper_certificate.py
python canonical_crossed_helper_certificate.py --kappa rel
python canonical_crossed_helper_certificate.py --kappa reverse_rel
python canonical_crossed_helper_certificate.py --kappa affine_a
python canonical_crossed_helper_certificate.py --kappa affine_b
```

`symmetry_k_calibration.md` records the earlier direct replacement of rho7
by primitive symmetry while retaining a canonical helper.
`canonical_membership_vacuity_obstruction.md` gives a concrete obstruction
to inferring full fresh membership vacuity from one canonical binder per
atom. The specialization note also gives a model showing that adding
universal self-specialization does not make rho6 redundant in the logical
basis. These are logical countermodels, not alleged models of the full K
theory.

## Proof convention and limits

The unchanged native propositional bridge uses rho8 **and rho6**. Rho8
supplies K/S/Peirce, rho6 supplies explosion for the literal falsehood
`F=Rel(0,0)=1`, and the resulting classical calculus justifies the
truth-table-checked `TAUT` leaves. It does not use a deleted equality row,
an equality helper, or a K axiom. Every GEN node has a closed theorem as
its premise. The complete equality-interpretation certificates reject
primitive symmetry, rho7, Eq-vacuity, arbitrary substitution, and
alpha-conversion as leaves unless that premise is expressly part of the
variant being compared.

The scripts check finite instances of uniform constructions explained in
the accompanying notes. They are not presented as new Rocq or Lean
machine-halting theorems. The source compiler, initialization, direct
transition folds, and binary runtime have their own candidate-specific
verification records in the main construction package.
