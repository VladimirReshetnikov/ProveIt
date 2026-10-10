# Verification summary

The mathematical proofs are in `article.tex` / `article.pdf`. The following are the executed finite and numerical checks, not a claim of independent peer review or proof-assistant formalization.

## Exact algebra

`exact_verification.json` records **826 exact assertions**, using SymPy 1.14.0. It checks finite Newton identities at sizes 1–10; regulator conversion through depth 4 and Laurent coefficient 2 (including all pole coefficients at those depths); first-order resonance coefficients for m=1–12 and n=1–48, with logarithms treated as independent formal symbols except log(1)=0; and nonpositive-order rational polylogarithm expansions through derivative index 8.

`finite_parts.json` records the harmonic, diagonal finite-part, and difference formulas through depth 4. Its g_r means gamma_r(a), not the article's depth coefficient g_d(a). This different machine-output naming is declared in that JSON. `resonance_polynomials.json` records the polynomial portions Q_m for m=1–6.

## Floating-point diagnostics

All three numerical suites used **60 decimal-digit working precision**. That is not a guarantee of 60 correct digits, and no rigorous interval certification is claimed.

- `numeric_verification.json`: **99 comparisons**, largest scaled residual approximately 3.34552884136e-50 and largest absolute residual approximately 1.12991413995e-48. Acceptance threshold: 1e-42 after scaling by max(1, |lhs|, |rhs|). Includes finite-radius Cauchy extraction of raw diagonal zeta finite parts; it does not rely on unstable infinitesimal differentiation of a boundary polylogarithm at integer order.
- `higher_jet_verification.json`: **960 coefficient comparisons**, m=1–6, n=1–32, derivative orders 0–4. Largest scaled residual approximately 7.15646756954e-60. The recurrence and Bell-factor formula are separate constructions.
- `cyclotomic_verification.json`: **16 product comparisons**, genera 2–5, parameters a=1 and 1.3, at fractional resonances and nearby complex spectral points. Largest scaled residual approximately 1.01404315621e-60.

Thus 1,075 floating-point comparisons were executed, in addition to the 826 exact assertions. These are finite diagnostics of the implementations. The theorems for all orders and all allowed parameters follow from the proofs in the article.

## Replay

Run `python code/run_checks.py`, or each script separately. Replaying rewrites its corresponding result JSON and therefore changes checksums. The quick option runs only the exact and higher-jet suites.
