# Parity and main-root saturation in eleven integers

`parity_saturated11_native.json` is a polynomial in eleven unrestricted
integer inputs, with exact total degree 924 and a 107-operation arithmetic
circuit. `parity_saturated11_short.json` has the same domain, degree 840,
and 108 operations. Both have ordinary proofs that their lack of integer
zeros is equivalent in ZFC to Con(ZFC), using the retained native/refutation
calibration. The complete new argument is `PROOF.md`; `REVIEW.md` records
an independent check within this AI-assisted workflow.

The construction composes package 132's main-root saturation, package
131's parity guard, and the exact product-square finalizer used in package
133. The congruence of the budget modulo sixteen makes budget minus four
nonsquare without the old scaling. This and the finalizer identity save
two operations at unchanged degree from the matched 109/924 and 110/840
parents.

Every live binary multiplication, addition, and subtraction counts,
including squaring and multiplication by a fixed numeral. Other registers
are polynomial abbreviations, not unknowns. The six fixed coefficients
are fully specified in `coefficients/`, including payloads, hashes, the
machine/table seed, and the finite reconstruction code. They are the whole
source34 tuple; they must not be interchanged with the different tuple
in the ten-positive-variable component.

Run with Python 3.10 or newer, using only its standard library:

```sh
python3 -B verify.py
python3 -O -B verify.py
```

The checker writes `CHECK.json` or `CHECK_OPTIMIZED.json`. The root release
checker copies this directory before running it, leaving the sealed
release intact. It reconstructs all fixed numerals, authenticates 109
retained dependencies, checks local free-polynomial identities, validates
every live graph node, proves the full leading monomial, and rejects three
corruptions. `build.py` regenerates both DAGs and the metrics; run it on a
copy when preserving release hashes.

`SOURCE_PINS.json` is the inherited dependency seal. Its historical
comparison commit is retained verbatim. The current comparison snapshot is
`1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`, as recorded at the release root.
`RESTORED_DEPENDENCIES.json` maps exact hashes to their current repository
copies. Parent proof documents are included at this component's root.

Finite checks do not prove the unbounded Pell or calibration statements.
No fresh complete Lean/Rocq or internal-ZFC proof object is supplied.
New material uses the root MIT No Attribution license; inherited source
licenses and notices appear in `licenses/` and `source/`.
