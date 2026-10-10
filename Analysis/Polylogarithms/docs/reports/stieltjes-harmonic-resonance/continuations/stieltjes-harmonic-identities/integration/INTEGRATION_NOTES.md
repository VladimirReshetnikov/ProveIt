# Integration notes

## Snapshot and scope

All repository comparisons use commit `fc4d3bf80534ad7c901d3b8c9e71baf2df0064ed`. `source_audit.json` contains the complete source record. The audit is targeted: it examines the relevant manuscript chapters and the mathematical structure and research questions of five incoming reports. It is not an audit of every proof in the 417-page manuscript.

## Proposed integration map

| New source | Main labels | Intended destination or dependency |
|---|---|---|
| `sections/conventions.tex` | `eq:periodic-family`, `eq:G-definition` | Align with existing distribution and Stieltjes conventions; most foundations are already present. |
| `sections/dilation.tex` | `dil:master`, `dil:contact`, `dil:transfer`, `dil:allindices`, `dil:loggamma` | Extend the integration/distribution chapters and answer CL's unequal-dilation question and RJ's scale/trace question. |
| Base subsection inside `sections/dilation.tex` | `base:theorem`, `base:Jgenerator` | Existing bilinear closure rederived for self-containment. Reuse the manuscript theorem if its precise normalization agrees. Do not list as a new discovery. |
| `sections/trilinear.tex` | `lem:Tentire`, `thm:sixcone`, `thm:triple-jets`, `eq:triple-digamma`, `cor:triple-primitives` | Extend the integration chapter with separated triple correlations. Answers three-factor questions in RJ, CL, CC and the coordinate component of RC's G3. |
| `sections/harmonic.tex` | `harm:thm:gamma-generating`, `harm:cor:rational`, `harm:thm:moving-pole` | Add the uncolored shifted harmonic calculus alongside the existing depth and generalized harmonic material. |
| First part of `sections/gauss_stieltjes.tex` | `gs:master`, `gs:spectral-jets`, `gs:mixed-jets`, `gs:rational-Lerch` | Add the normally convergent Gauss–Stieltjes coefficient construction and its polylogarithmic boundary interpretation. |
| Negative-balance part | `gs:successive-subtraction`, `gs:residue-rigidity`, `gs:resonant-jet`, `gs:central-minus-one` | Add exact continuation through every negative integer balance and its resonance constants. |
| Historical correction part | `gs:choi-master`, `gs:choi-pure`, `gs:choi-mixed` | Add proved corrected harmonic identities with the precise external source citation and audit note. |
| `sections/surviving_conjectures.tex` | `eq:source-current-S6`, `eq:source-current-S8` | Context and status only. These are existing conjectures, not new theorems. |

## Required normalization decisions

1. Preserve the ordinary Stieltjes sign convention `(-1)^m gamma_m(a)/m!` at `s=1+u`.
2. Preserve the Fourier coefficient phase `exp(-i pi lambda sgn(n)/2)` at Hurwitz order `1-lambda`.
3. Distinguish the pullback distribution from the cutoff finite part in the unscaled coordinate `x-x0`. The exact difference is part of the theorem.
4. For the bilinear affine theorem, set `p=dP`, `q=dQ`, `gcd(P,Q)=1`, and `c={P b-Q a}`. The separation condition is `c != 0`.
5. For triple products, retain pairwise distinct shifts. None of these proofs defines coincident products by fiat.
6. Keep coefficient factorials explicit: `E_r(n)=r! E_{n,r}` in the Choi section. The exact generator records the `n=0` exception when both mixed orders are zero.
7. At negative balance, use reciprocal Gamma germs at their zeros. Expressions formed with logarithmic derivatives are valid only away from those zeros.
8. The single-factor primitive formula is a particular explicitly normalized choice. Its use in a triple ordinary correlation is the extension here.

## Targeted repository correction

In `ProveIt_Stieltjes_Convolution_2026-10-10.zip`, inner `ProveIt_Stieltjes_Convolution_2026-10-10/article.tex`, lines 1118–1121, qualify the assertion that different affine frequencies create multiple independent Fourier indices. For two integer frequencies, the relation `p n+q m=0` always has one parameter. `proposed_corrections.tex` provides replacement prose. No central convolution theorem is refuted.

## External correction

For Choi (2014), DOI `10.1155/2014/501906`, publisher PDF printed page 6:

- Equations (41)–(46): divide their right-hand sides by two; equation (46) also needs the numerator correction below.
- Equation (40), second formula: the final term is `-120 H_n^(6)`, not `-120 H_n^(5)`.
- Equation (46): use `45 H_n^3 (H_n^(2))^2` at the indicated partition term.

The master theorem proves the intended polynomial identities in all orders. It does not claim that the printed conjectures remained open in 2026 or that these are the first historical corrections. The article supplies a separate elementary proof of the first factor-of-two correction.

## Status boundaries

- Current S6 and S8 are still conjectures. Their exact source formulas and vectors are retained in `source_audit.json`.
- The older, rigorously rejected S8 vector is a different vector. Its exclusion does not refute the current S8 formula.
- The uncolored harmonic theorem does not insert `(-1)^n` by choosing the parameter `1/2`.
- A colored Tornheim representation is not a proof of a reduction to a smaller constant basket.
- Numerical residuals and symbolic finite sample checks do not prove the general theorems; the analytic arguments are in the article.
- No arithmetic independence, global novelty, or proof-assistant certification is asserted.

## Build portability

The article uses ordinary LaTeX packages and a manually maintained bibliography. TeX section labels have component prefixes to reduce collisions. Some local symbols (`G`, `A_j`, `E_r`) are reused in different sections and should be renamed to match the repository's global notation during integration. All relevant meanings are explicit where introduced.

The source checkout and the original incoming archives are not bundled. The package includes source identifiers and the research deliverables needed to review and integrate the results.
