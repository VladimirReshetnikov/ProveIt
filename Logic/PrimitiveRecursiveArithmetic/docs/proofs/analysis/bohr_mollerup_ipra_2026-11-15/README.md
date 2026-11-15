# Constructive Bohr–Mollerup theorem in iPRA

This archive gives a finitary constructive version of the Bohr–Mollerup
theorem designed for intuitionistic primitive recursive arithmetic.

## Main files

- `paper/bohr_mollerup_ipra.pdf` — complete human-readable argument.
- `paper/bohr_mollerup_ipra.tex` — LaTeX source.
- `lean/BohrMollerupOutline.lean` — structured Lean scaffold.
- `lean/LEAN_ROADMAP.md` — module-by-module path to a complete object-level
  formalization in the ProveIt `ConciseIPRA` development.
- `code/bm_bounds.py` — exact-rational certificate generator and verifier for
  the constructive Euler brackets.
- `code/test_bm_bounds.py` — regression tests.
- `sample_certificate_half.json` — sample enclosure certificate.
- `SOURCES.md` — source and repository references.
- `MANIFEST.sha256` — checksums for the delivered files.

## The theorem proved

Because first-order iPRA cannot quantify over arbitrary real functions, the
internal result is a theorem schema for each fixed primitive-recursive
interval presentation `F` on positive rational codes. Positivity carries a
rational lower witness, and log-convexity is replaced by rational
multiplicative convexity:

```text
F(((s-j)x + j y)/s)^s ≤ F(x)^(s-j) F(y)^j.
```

Under normalization `F(1)=1`, recurrence `F(x+1)=xF(x)`, and that convexity
condition, every rational value of `F` equals the explicitly constructed gamma
presentation. With a primitive-recursive local modulus, the equality extends
to regular positive real names.

## Running the exact checker

```bash
cd code
python3 test_bm_bounds.py
python3 bm_bounds.py 1/2 --bits 6 --json ../certificate.json
python3 bm_bounds.py --verify ../certificate.json
```

Certificate verification uses integer arithmetic and Python `Fraction` only.
The decimal enclosure printed by the CLI is informational and is not used in
verification.

## Formalization status

The mathematical proof and algorithms are fully developed in the report. The
Lean deliverable is an outline with explicit theorem interfaces and remaining
milestones; it is **not** a completed machine-checked proof. No Lean toolchain
was installed in the artifact-building environment, so the outline was not
compiled here.
