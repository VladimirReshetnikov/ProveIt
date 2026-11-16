# Verification and completion status

| Component | Status | What has actually been checked |
|---|---|---|
| Human mathematical manuscript | Developed | The paper gives finite quantitative arguments, explicit hypotheses, moduli, and iPRA arithmetizations. |
| LaTeX/PDF | Built | `latexmk -pdf -interaction=nonstopmode -halt-on-error` succeeds; the final PDF has 46 pages. |
| Exact certificate program | Passed | 96/96 assertions pass using only integers and `fractions.Fraction` for proof-relevant arithmetic. |
| Coverage intervals | Passed | Exact rational enclosures for `P(|Z| ≤ n)`, `n=1,…,6`, have width about `1.2154e-63`. |
| Moment/Hermite tests | Passed | Recurrences and polynomial identities are checked through the finite ranges recorded in `validation.json`. |
| Lean finite layer | Blueprint | Concrete definitions and module boundaries are supplied; the files were not compiled in this environment. |
| Deeply embedded iPRA derivations | Not yet constructed | No file in this packet is claimed to inhabit the headline types `[] ⊢[PRAAx] φ`. |
| Native concise-calculus transport | Planned | Apply ProveIt's checked `pra_iff_native` only after the ordinary `Prf PRAAx` derivations exist. |

## No hidden endpoint claim

The `.lean` files are specifications and implementation plans. They deliberately contain no `sorry`-based declaration of the main analytic theorems and introduce no new mathematical axiom presented as a proof. Analytic contracts are described as data that later modules must instantiate with explicit certificate producers and object-theory derivations.

## Proof-relevant versus diagnostic computation

All certificate endpoints and comparisons in `evidence/validation.json` are exact rationals. Optional `mpmath` output is stored under `floating_diagnostics_not_proof` and is never used to decide a check.
