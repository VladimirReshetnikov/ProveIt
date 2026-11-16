# Source manifest

Inspected on 16 November 2026.

## Requested reference pages

1. Wikipedia, "Beta function"
   - https://en.wikipedia.org/wiki/Beta_function
   - Used only as a theorem/formula inventory. The report independently audits domains and correctness.

2. Wolfram MathWorld, "Beta Function"
   - https://mathworld.wolfram.com/BetaFunction.html
   - Equation numbers (1)--(43) are used as inventory labels.

3. NIST Digital Library of Mathematical Functions
   - https://dlmf.nist.gov/5
   - https://dlmf.nist.gov/8
   - Used as a standard reference for Gamma/Beta and incomplete-Beta identities; the constructive proofs and bounds are supplied in the report or isolated as remaining obligations.

## ProveIt repository

Repository:
- https://github.com/VladimirReshetnikov/ProveIt

Inspected paths on the `main` branch:

- `Logic/PrimitiveRecursiveArithmetic/README.md`
  - Status boundary between checked libraries and unverified research packets.

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
  - Native scalar core and the checked `pra_iff_native` / `native_iff_pra` bridge.

- `Logic/PrimitiveRecursiveArithmetic/Derivations/README.md`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/`
  - Checked embedded iPRA arithmetic infrastructure: finite sums/products, powers, factorials, order, division, search, pairing, and permutation.

- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/gamma_ipra/README.md`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/gamma_ipra/paper/sections/01_foundations.tex`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/gamma_ipra/paper/sections/03_integrals.tex`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/gamma_ipra/paper/sections/04_identities.tex`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/gamma_ipra/paper/sections/08_formalization.tex`
  - Effective Gamma, finite calculus, beta subsection, reflection/multiplication, and formalization route.
  - This is a research packet. Its own documentation says the full analytic Lean formalization and `Prf PRAAx` derivations remain incomplete.

## Artifact provenance

- The report text, Lean outline, exact-rational checker, and theorem inventory were created for this task.
- `code/beta_finite_certificates.py` uses only Python integers and `fractions.Fraction`; it does not call a transcendental numeric oracle.
- No source-page text or repository file is redistributed wholesale in this archive.
