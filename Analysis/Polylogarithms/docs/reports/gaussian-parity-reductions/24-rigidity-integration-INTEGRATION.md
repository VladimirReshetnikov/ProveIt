# Integration guide

Baseline: `d00eba30c1ce73ee5cfbeb50bde9095246b9c25c`.

## Confirmed correction

Target: `Analysis/Polylogarithms/docs/manuscript/chapters/03-algebraic.tex`, paragraph immediately after equations `bloch:eq:goldenP3` and `bloch:eq:sgP3`.

The even-weight assertion conflicts with the displayed definition `bloch:eq:Pm`. For every real `0<x<1`, all terms inside that definition are real, so its imaginary part, and hence `P_(2j)(x)`, is zero. The ordinary even-weight Li identities may remain valid; their asserted interpretation as nonzero zeta multiples under this particular P is false.

The proposed replacement and unified diff are supplied. The diff was checked against the baseline without applying it. It changes only the indicated paragraph. It deliberately makes no status change to the surrounding higher-weight ordinary formulas.

## Theorem integrations

| Destination | Material | Status change |
|---|---|---|
| Algebraic chapter, before or after the non-golden bases | `article/sections/ladders.tex`, first section | Add complete classification, signed cyclic count, degree bound, and exact count. |
| Algebraic chapter, reciprocal minimal Pisot ladder | `article/sections/ladders.tex`, second section | Promote the plastic Li2 and Li3 formulas with their complete proofs; add the log-free identities. |
| Depth chapter, equation `gauss:eq:S4-closed` | `article/sections/gaussian.tex`, `code/verify_s4.py`, `results/S4_certificate.json` | Promote this equation to a proved, computer-assisted exact identity. Retain the explicit single-divergence regularization explanation. |
| Alternating-harmonic research report | `article/sections/saddle.tex` and figure | Add the proportional-depth asymptotic theorem and compact-parameter qualification. |
| Gamma chapter or its supporting research report | `article/sections/gamma.tex` | Add the fixed reflected-exponent theory, residue identity, and formal Appell result. |
| Research register | `article/sections/research.tex` | Replace the now-resolved S4 and pure-complement classification questions with the more precise next problems. |

The section files use standard theorem environments and the macros declared in the supplied main TeX file. If incorporated into the book, adapt section levels and equation prefixes to its conventions. Keep the exact series/word convention near the Gaussian theorem: it fixes both the cumulative colors and the depth signs.

## Proof and claim boundaries

- The Gaussian certificate is finite rational linear algebra backed by proved analytic relation schemas. It is not a numerical integer-relation test or a formal proof-assistant development.
- The 911-row count describes the supplied certificate. No minimality is asserted.
- The all-exponent complement classification uses the cited Ljunggren–Tverberg theorem. The finite polynomial survey is corroboration, not its proof.
- Pure complement equations do not capture all product unit relations and do not imply a maximal ladder weight.
- Reflected asymptotics hold for each fixed nonnegative integer reflected exponent. The infinite late-index series diverges; only finite truncations and the stated remainder theorem are valid.
- The Appell claim is tied to the canonical formal polynomials and to Conjecture 5.5 in the inspected March 2010 author preprint. Do not replace it with an unconditional claim of numerical coefficient uniqueness or of historical priority.
- The adjacent plastic Li4 identity and the unresolved higher-weight identities remain separate proof obligations.
