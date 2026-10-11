# Polylogarithms and their Arithmetic Bridges

The collective manuscript, authored by **ProveIt Contributors**, is now
organized as four volumes. Each has its own source and compiled PDF.

| Volume | Material | PDF | Pages |
|---|---|---|---:|
| I | Polylogarithm identities, cyclotomic coordinates, algebraic ladders and Gaussian/Eisenstein reductions | [Polylogarithm Identities and Arithmetic Reductions](volumes/volume-1-polylogarithm-identities.pdf) | 128 |
| II | Signed kernels, angular and all-depth zero geometry, exact computation and experimental discovery; literature appendix | [Signed Kernels, Zero Geometry and Experimental Discovery](volumes/volume-2-signed-kernels.pdf) | 119 |
| III | Hurwitz jets, Stieltjes integration/differentiation, finite parts, Gamma correlations, twists and Stieltjes zeros | [Hurwitz Jets, Stieltjes Calculus and Gamma Correlations](volumes/volume-3-hurwitz-stieltjes.pdf) | 184 |
| IV | Gamma grids, CM lattice periods, class products and Herglotz arithmetic | [Gamma Grids, CM Periods and Herglotz Arithmetic](volumes/volume-4-cm-and-herglotz.pdf) | 83 |

The volumes partition all twelve chapters and the literature appendix.
Chapter, theorem and equation numbering is retained so research-report
citations stay stable. Cross-volume references link to their exact PDF
destinations; keep the four PDFs together. Each volume has its own contents
and the shared bibliography of 124 references. The scientific text is shared
through chapter files and [preamble.tex](preamble.tex), avoiding duplicate
copies of proofs. See [volume sources and build instructions](volumes/README.md).
The [combined source](polylogarithms.tex) and its
[479-page combined snapshot](polylogarithms.pdf) remain available.

The [inventory](source-inventory.json) accounts for **894 textual source
files**, including overlapping assembled articles, fragments and correction
registers. The [editorial ledger](EDITORIAL-LEDGER.md) maps their mathematical
status and identifies pending research integration. Sixty incoming
archives are preserved as **2,273 original tracked members**. All their isolated
replay suites pass; preservation and successful finite replay do not imply
that every new analytic theorem has already been integrated. The imported
ZIPs have been retired from the drop zone under its intake procedure; the
arrival commits and recovery paths remain recorded in
`verification/*incoming-archives.json` and the retirement records. Thirteen ignored
SHA256SUMS members remain recoverable in their recorded arrival archives; the
existing ignore rules were followed without manifest verification. The latest five
packages extend the harmonic-resonance and Stieltjes-correlation spines.
Volume III now proves the all-index fixed-coordinate periodic contact law,
its Bernoulli primitives and ordinary vanishing-weight Hurwitz identities.
A self-contained first-resonance Rogers-Dougall proof gives all fixed mixed
Gamma derivatives and a weighted trigamma-square evaluation. That experiment
leads to an all-orders zeta-tail identity with an independent Euler partial-
fraction proof. In particular,

```text
sum(n>=0) (2n+1) (zeta(3)-H_n^(3))^2 = 3 zeta(4)/2,
sum(k>=1) k (2(zeta(3)-H_(k-1)^(3))-k^(-3))^2 = 3 zeta(4)-zeta(5).
```

Volume I retains the weighted real arctangent Li3 family, its signed
inverse-hyperbolic companion and the 7 zeta(3)/2 endpoint. Seventeen further
committed arrivals remain in the drop zone pending their own preservation
and proof audits. Other incoming analytic claims retain the ledger's
pending scope; S6 and S8 remain open.

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
conjectural. The real-order core is now integrated in Chapter 5, with new proofs of unrestricted slit-plane nonvanishing, angular uniqueness, subcritical radial motion, Gaussian fixed-total monotonicity, a unique axis maximum and the sharp critical/subcritical Euler constant pi/4+log(2)/2. Its location and height now have rigorous rational enclosures. A separate Euler-kernel contraction proof establishes the sharp universal constant C(b*) for all a>=0,b>0, with equality only at a=0,N=1 and the maximizing inner order. The rational budget 57/50 is valid throughout the positive quadrant. Strict log-concavity of C(b)-1 also gives Turan inequalities. Bessel, full Cayley, Lerch, uniform-transition, golden-seed and Herglotz continuations remain on the active proof-audit and integration agenda.

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

The latest canonical milestone integrates the complete forty-two-row rational
tetralogarithm proof, including lower-weight descent, branch constants and the
additional twenty-five-argument specialization. An independent ordered-tensor
implementation verifies the printed canonical table and rejects a changed
coefficient. Chapter 5 proves the full leading-index-one normalized-radius
trichotomy for all b>0 and the strictly smaller 9/8 Euler budget for every
truncation N>=2. The unsupported elementary-value impossibility claim is
corrected, and two transport-notation slips are repaired.

All eleven new isolated default suites pass. The radial replay checks the
full 2,304-cell cover and 4,609 root boxes. The exact S14 proximity verifier
also passes, while equality remains conjectural. Finite certificates support
the separately audited analytic proofs; they do not promote the other
preserved continuum claims automatically. The active research programme continues with functional certificates,
unresolved finite-weight identities and their experimental discovery.
Geometric and asymptotic continuations retain their audited scope.

The all-depth signed-kernel development is now integrated in full, including
minimal positive compensation, the complete angular count, uniform
expansions, explicit logistic roots and positive integral identities. A
collective several-color divided-difference identity yields confluent
resolvent polynomials at every order. Its Gaussian logarithmic moments have
an exact coefficient formula in Q[i,pi,log(2)], including two printed real
weight-two integral evaluations. The proof uses beta moments and parameter
differentiation; 117 finite coefficient and six partial-fraction checks pass,
with thirty independent 65-digit quadrature diagnostics. Wolfram supplies
45 exact checks and six further numerical comparisons.

A separate positive pair decomposition strengthens the Stieltjes radial
phase theorem and proves theta'(rho)<0 for every a>=0,b>0. Its universal
disk range is sharp by an explicit two-atom counterexample at every
prescribed larger radius. This does not assert a uniform normalized-radius
sign or settle the unresolved arithmetic Gaussian sums. Experiments,
finite exact arithmetic and full analytic identities keep distinct roles.

The Stieltjes correlation material now forms a single proof chain in Chapters
8 and 9: the entire Fourier Hurwitz family, canonical finite parts, the Bell
convolution algebra, all-index shifted closure, coincident subtraction and
convergent collision expansion, all primitive orders, ordinary log-Gamma
correlations and every circular log-Gamma convolution power. Laurent residues
then give the derivative contact law and every translated polygamma product.
These proofs share one normalization and distinguish ordinary integrals from
finite parts. The original pointwise derivative tower remains valid.

A collective continuation proves the exact dilation action and its logarithmic
contact corrections at every Stieltjes and derivative order. The normalized
trace translates the convolution generator by minus log(q). Covering pullback
and distribution trace have different contact supports and signs; the proof
computes both, including the all-order polygamma specialization. Independent
SymPy checks cover 224 exact identities plus a corruption control. Wolfram
15.0.1 supplies 36 further exact checks and four direct subtracted-integral
diagnostics; another fifteen diagnostics use 60 decimal digits. Numerical
checks are not interval certificates or substitutes for the all-index proofs.

All five new packages received complete isolated replay, including the full
seven-script calculus run and all four resonance suites. Uniform resonance,
joint Herglotz limits, nonseparable module theorems, higher negative-integer
collision regularity and Hankel developments remain pending canonical analytic
audit. Successful finite replay does not promote those claims to proved status.

The ninth intake adds Gauss-Hurwitz, Mellin-dilation, nested-harmonic,
Stieltjes-harmonic and Polylogarithm-Stieltjes critical continuations. The
corrected Choi pure and mixed harmonic families are now proved at every order
by a normally convergent Gauss generating function; the fifth- and sixth-order
conjecture cases follow. The n=0 term at zero total order is explicit. An
independent elementary proof and native Wolfram integral reject the printed
factor-two normalization. Seven further native mixed coefficients pass exactly.
Remaining new Gauss jets, Mellin formulas, unequal-grid products, nested
regulator conversions, triple correlations, near-critical crossing and Cayley
depth proofs retain their pending canonical analytic integration status.
The current inventory includes these preserved, explicitly pending sources.

The ninth full isolated replay also passes: Gauss (512 exact checks and 64
65-digit diagnostics), nested jets (826 exact assertions and 1075 numerical
comparisons), harmonic identities (128 exact checks and all five components),
Mellin-dilation (742 exact assertions and 77 diagnostics through nine entry
points), and the complete exact/numeric/Euler critical-transition suite.
The nonzero thirty-term formal S6 projection is preserved with its explicit
qualification: it makes no assertion about the numerical residual.

The tenth intake adds endpoint-regulator and twisted harmonic-Laurent reports.
Both full isolated suites pass. The twisted Lerch family now has a complete
canonical proof chain: all nonintegral twists, full Dirac residues, all-index
Bell and reflected products, covariant contact corrections, rational Hurwitz
coordinates, the convergent half-twist integral and its quarter-Gamma value,
unique covariant primitives, and exact zero-frequency subtraction back to
the untwisted normalization. Its shifted-harmonic Laurent developments and
the endpoint-regulator report remain explicitly pending canonical integration.

A collective continuation gives a Dirichlet beta mixture for any finite number
of unequal twists in one interval between integers. Positive integer orders
admit an exact finite partial-fraction reduction to elementary covariant
kernels; repeated twists combine by addition. Independent exact controls
cover 64 identities and a rejected corruption, alongside 25 separate 60-digit
diagnostics including zero and negative modes and ordinary wrapped integrals.
Wolfram 15.0.1 confirms 25 further exact identities and nine 70-digit branch,
endpoint and quarter-Gamma diagnostics. These numerical records are not
interval certificates. The real arctanh formula now uses an absolute value
in its logarithm; its derivative proof covers negative parameters and both
endpoints. The unsupported non-elementarity description is removed.
