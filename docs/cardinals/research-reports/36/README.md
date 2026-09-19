# Finite choice at measurable strength

## Contents

- `Cardinals5_Prikry_Finite_Choice.tex`: complete LaTeX source.
- `Cardinals5_Prikry_Finite_Choice.pdf`: compiled report with detailed English proofs.
- `finite_check.py`: deterministic, dependency-free finite algebra checks.
- `finite_check_results.txt`: actual output of the included checks.
- `build.sh`: reproducible three-pass pdfLaTeX build.

## Research contribution

The setting is an ordinary normal-measure Prikry extension V = M[c] at a
measurable cardinal kappa, with q the finite-difference class of the generic
cofinal sequence.

The main theorem proves the cyclic fixed-point criterion for nonempty finite
families of admissible labeling rules, including rules with arbitrary
ground-model label sets. It implies that no nonempty finite family of
selectors on the cofinal quotient is definable from q, ground-model sets,
and ordinal parameters. This answers the Prikry-extension question explicitly
posed in the supplied Cardinals4 synthesis.

The report also proves a profinite-density theorem for definable families of
ultrafilters on q. It constructs an explicit countably infinite such family,
whose phase image is exactly one integer orbit. Thus the least possible size
of a nonempty definable **local** ultrafilter family is exactly aleph_0.
The exact minimum for a nonempty **compact** definable local family is
2^(2^aleph_0), and the closure of the explicit countable family attains it.
This does not construct a countable definable family of **global** kernels.

Further results give sharp residue constraints for finite families of
finitely additive probabilities, exact periodic examples, and a measurable-
strength consistency package incorporating all the finite cyclic obstructions.
The package can hold when the canonical core regards kappa as its first
measurable cardinal, so the displayed normal trace does not concentrate on
smaller measurables.

## Scope and verification

The new arguments have conventional English proofs, not Lean formalizations.
Classical Prikry forcing facts are explicitly identified and referenced.
Earlier archive results and constructions are credited rather than presented
as new. Publication priority has not been exhaustively checked, and the
manuscript has not undergone independent peer review.

The Python program checks only finite permutation identities, indexing signs,
and exact rational residue frequencies. It does not verify forcing, HOD,
genericity, or consistency assertions. It is not a proof assistant.

The results do not prove that rigidity alone implies the cyclic obstruction
in arbitrary models, do not settle countable families of global kernels or
selectors, and do not prove inconsistency of ultraexactingness or I0.
The lower consistency bound for the package is supplied by its explicit
normal-trace clause, not by bare selector failure alone.

## Building

A standard TeX Live installation with pdfLaTeX and the packages named in the
source is sufficient. The typography uses `newpxtext` and `newpxmath`, the
same page geometry and heading conventions, and the Forest / Olive / Sage /
Pale palette from the supplied synthesis. No font files are distributed.

Run:

```sh
bash build.sh
python3 finite_check.py
```

The build script writes intermediate TeX files under `build/` and copies the
finished PDF into this directory. Python 3.9 or newer is required for the checks.

Prepared 18 September 2026 as a continuation of the user-supplied Cardinals4
archive. No changes were made to the original archive or its Lean development.
