# Gap-Six Reconstruction, Complex Harmonic Determinants, and Stieltjes Boundary Collisions

Research continuation for the ProveIt project, completed 12 October 2026.
Repository snapshot: c4036d60715916ae72dd18983782fdb182840b86 (11 October 2026).

## Read the article

The complete article is supplied as:

- Gap_Six_Harmonic_Determinants_and_Stieltjes_Collisions.pdf
- Gap_Six_Harmonic_Determinants_and_Stieltjes_Collisions.tex — assembled standalone source
- article.tex, sections/, and references.tex — modular editable source

The standalone source needs no other source files. Both source forms use standard
LaTeX packages; no external images or network access are needed to build.

## Main advances

1. **Complete gap-six moment reconstruction.** For every even q >= 8 and
   p=q-6, the first q centered harmonic-tail moments have full rank on the
   specified formal coefficient list and reconstruct every later moment.
   The proof combines an explicit analytic threshold b=q/2 >= 2048 with
   exact modular nonvanishing for every 4 <= b <= 2047.
2. **Complex rational harmonic degree.** The generic formal harmonic degree
   equals the generic harmonic-pencil rank for every nonzero complex rational
   weight. The core rational symmetric primitive theorem works over every
   characteristic-zero field and allows varying pencil kernels.
3. **Unequal-rate Stieltjes collisions.** The full singular expansion and
   fixed-coordinate constant are explicit for every pair of Stieltjes indices
   and argument-derivative orders, when the two positive shifts are fixed
   multiples of the same small parameter.
4. **Explicit identity families.** An all-order rational polygamma-tail sum,
   a fixed-size Hahn formula, a classification of adjacent-pole residue
   exceptions, classical-dilogarithm cutoff generators at every particle count,
   and a positive three-particle identity with a zeta-valued convergent integral.

## Proof and evidence

The article supplies analytic and algebraic proofs. The finite-field certificate
is part of the gap-six proof, not a numerical extrapolation. The independent
finite symbolic checks and high-precision quadratures have separately stated roles.

- results/gap_six_certificate.json: all 2,044 nonzero determinant residues,
  primality and denominator checks, plus independent normalizations.
- results/gap_six_14_20_example.json: exact integer coefficients and a complete
  finite telescoper for the worked (14,20) ordinary polygamma identity.
- verification/: eight mathematical verification programs and a runner.
- results/: complete generated evidence and execution logs.
- audits/: independent internal proof audits of the most sensitive arguments.
- provenance/source_manifest.json: pinned source inventory, archive hashes,
  and exact proof dependencies.
- provenance/inherited/: seven unchanged source sections supplied for comparison
  and proof-dependency inspection, with their original authorship.
- CLAIM_STATUS.json: machine-readable status and scope.
- INTEGRATION.md: precise proposed changes to the repository research frontier.

The formal rank results do not assert arithmetic independence of evaluated
constants. Modular residues prove nonvanishing, not signs, in the finite range.
Floating-point diagnostics are not certified error enclosures. The claims are
new relative to the inspected repository frontier; the bibliography and article
credit established methods and do not claim an exhaustive historical-priority search.

## Reproduce

Python 3.12.14, SymPy 1.14.0, and mpmath 1.3.0 were used.

    python -m pip install -r requirements.txt
    python verification/run_all.py
    python build.py

The verification runner stops on failure and saves a log for every program.
The collision quadratures are the slowest part. To run just their exact algebra:

    python verification/verify_collisions.py --exact-only

The build program assembles the standalone source and runs three pdflatex passes.
No shell escape is enabled. The source PDF was rendered and visually reviewed
before delivery; the QA record is in results/document_qa.json.

## Further questions and limits

The article proposes twelve concrete research questions, including gap eight,
a structural proof of gap-six signs, a uniform two-parameter moment theorem,
Gamma normalizations, residue-level cutoff classification, several-pole
polylogarithm compilers, unequal collision scales, and three-factor contacts.

The unrestricted all-pairs moment-prefix conjecture, the source's stronger
finite-range gap-six sign conjecture, and the manuscript's short Gaussian
S6 and revised S8 identities remain open here.

This research was prepared with ChatGPT and internally audited through
independently developed proofs and exact calculations. It is supplied for
integration and independent mathematical review; it is not externally peer
reviewed or formalized in a proof assistant.
