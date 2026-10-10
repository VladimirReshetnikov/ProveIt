# Polylogarithms and their Arithmetic Bridges

The collective manuscript, authored by **ProveIt Contributors**, is
[polylogarithms.pdf](polylogarithms.pdf): **375 pages, twelve chapters,
thirteen figures and 98 references**, with a literature appendix preserving
94 distinct historical question leads. Its editable source is
[polylogarithms.tex](polylogarithms.tex) and the files in `chapters/`.

The [inventory](source-inventory.json) accounts for **381 textual source
files**, including overlapping assembled articles, fragments and correction
registers. The [editorial ledger](EDITORIAL-LEDGER.md) maps their mathematical
status and identifies pending research integration. Twenty-one incoming
archives are preserved as **865 byte-identical members**. All their isolated
replay suites pass; preservation and successful finite replay do not imply
that every new analytic theorem has already been integrated. The imported
ZIPs have been retired from the drop zone under its intake procedure; the
arrival commits and recovery paths remain recorded in
`verification/*incoming-archives.json` and `verification/incoming-retirement.json`.

The preceding milestone proves the CM class-product formulas and the recorded
genus ratios, develops a rational principal-point nonvanishing bound, and
proves exact quadratic degree at every even weight for discriminants
-15, -20 and -39. Further genus results give norm identities, nine additional
explicit evaluations, and the full finite cluster set [1/2, infinity) for
the weight-12m ratios at discriminant -15. An independent finite-field
certificate replaces a failed-search argument for the discriminant -39
cube-root obstruction. The latest reports also correct Clausen parity,
unsupported numerical nonreduction, the published plastic-field sequel,
and missing golden-ladder notation.

The new integral development in Chapter 9 proves an all-ring raw-point
basis, a universal unit minor, a weighted resolution, reflection torsion,
modular rank loci and complete one-parameter Smith exponents. It also
proves an exact product law for separable multivariable jets, checked by
210 independent raw binary matrices. The level-12/15/30 certificates give
all-order identities with pole-corrected derivatives. General multivariable
extensions and numerical period independence remain open.

The new S8 candidate is distinct from the old rigorously rejected vector.
Its exact normalized residual enclosure is below `1e-355`; it and S6 remain
conjectural. The real-order core is now integrated in Chapter 5, with new proofs of unrestricted slit-plane nonvanishing, angular uniqueness, subcritical radial motion, Gaussian fixed-total monotonicity, a unique axis maximum and the sharp critical/subcritical Euler constant pi/4+log(2)/2. The maximum has exact bracket 1<b*<2; its decimal location remains diagnostic. Bessel, full Cayley, Lerch, uniform-transition, golden-seed and Herglotz continuations remain on the active proof-audit and integration agenda.

Original drafts, code, data and PDFs remain historical evidence. This book is
the canonical reading artifact.

The development follows mathematical dependency: conventions and Nielsen
calculus; cyclotomic coordinates; algebraic arguments and ladders; depth,
inverse-color reductions and harmonic sums; signed kernels and certified
computation; gamma certificates; CM lattices;
integrated zeta jets; differentiated jets and uniform distribution ranks;
Stieltjes zero geometry and spectral asymptotics; Herglotz arithmetic and
optimal truncation; and experimental discovery. Experiments motivate the
exact identities, rank proofs and analytic asymptotics, with proof status
stated at each transition.

The [validation report](VALIDATION.md) records fresh native Wolfram and
independent Python checks, exact rational certificates, the converged build
and rendered review. [WORKLOG.md](WORKLOG.md) records the active research continuation.
The earlier five-package intake added the exact S4 proof, complementary-depth transport,
pure-complement classification, conductor descent and trace jets, proportional
harmonic saddles, sharp reflected-moment remainders, and rational Herglotz
derivatives with exponentially small oscillation. S6 remains a conjecture
despite the strengthened exact normalized residual enclosure below `1e-355`.

Numerical period independence and minimal depth are not inferred from failed
searches. Gamma completeness beyond the stated relation system and Stark
regulator predictions retain their conjectural scope. There is no
proof-assistant formalization.

## Reproduction

From this directory, with LuaLaTeX, Python (mpmath, sympy, PyMuPDF and Pillow)
and Wolfram Language available:

```powershell
python verification/check_document.py
python verification/check_identities.py
wolfram -script verification/check-identities.wls
python verification/check_additional_corrections.py
python verification/check_nielsen_inversion.py
python verification/replay_ranks.py
python verification/replay_cyclotomic.py
python verification/replay_spectral.py
python verification/replay_incoming.py --part rigidity
python verification/replay_incoming.py --part distribution
python verification/replay_incoming.py --part conductor
python verification/replay_incoming.py --part complement
python verification/replay_incoming.py --part reflection
wolfram -script verification/check-incoming.wls
python verification/check_reflected_sharp.py
python verification/build.py
python verification/inspect_pdf.py --render-directory C:/path/to/local/review
python verification/verify_receipts.py
```

`build.py` runs three serial LuaLaTeX passes. The committed hash receipts pin
the reviewed PDF: a rebuild may differ in binary metadata and requires its
own rendered review. `verify_receipts.py` checks the committed evidence; it
does not rerun mathematics or confer review on a changed artifact. Additional
continuation replays and their exact configurations are listed in
[verification/REPRODUCTION.md](verification/REPRODUCTION.md). Every replay
uses a separate manuscript output directory, preserving historical receipts.
