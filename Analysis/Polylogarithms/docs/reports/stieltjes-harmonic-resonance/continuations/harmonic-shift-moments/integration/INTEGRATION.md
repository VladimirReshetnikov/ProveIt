# Proposed ProveIt integration

## Baseline and scope

This package was developed against manuscript/incoming revision `921b58f1099568bfefa28a556470e4b29e94eb3b`. The historical mixed spectral report and earlier exact identities archive were read at `5a790187c8e186e41e2b990b4941cb7a1a3c7b6b`.

The source audit was focused on the material used in these proofs. It did not certify the entire manuscript. No newly false theorem was identified in the selected source claims. The qualifications below prevent invalid extensions when the new results are integrated.

## Suggested placement and dependencies

| New module | Place after / depend on | Principal labels |
| --- | --- | --- |
| `sections/02_shift_germs.tex` | Entire harmonic difference and independent-order relative Hurwitz character | `hsh:germ`, `hsh:boundary`, `hsh:primitives`, `hsh:radius`, `hsh:rank` |
| `sections/03_bell_moments.tex` | Mixed spectral Dougall double-zero identity | `bell:rank`, `bell:image`, `bell:sixrref`, `bell:eightrref`, `bell:quartic`, `bell:harmonic` |
| `sections/04_harmonic_powers.tex` | Exact resonant raw harmonic-power continuation and centered parity result | `hpnew:generator`, `hpnew:uniformspan`, `hpnew:Bernoulli`, `hpnew:oddorders`, `hpnew:threerows`, `hpnew:upoles` |
| `sections/05_collisions.tex` | Fixed-rate periodic digamma collision calculations | `hc:main`, `hc:arcs`, `hc:hierarchy`, `hc:quartic`, `hc:middle-derivative` |

Preserve the four label prefixes when splitting or moving sections. The standalone preamble defines the small number of notation macros used by these files. Reconcile theorem environments and bibliography keys with the destination manuscript; no custom font assets or generated figures are needed.

### Exact antecedent identification

In `ProveIt_Independent_Orders_2026-10-11.zip`, `sections/02_hurwitz.tex`, the labels `eht:rec`, `eht:lower-shift`, and `eht:ones-Gamma` imply the exact specialization

`D_r(s;a) = H_{1,a}(s,{1}^r)`

where `H` here denotes that report's relative character, not an ordinary harmonic number. The new section proves this identification at `hsh:relativecharacter`. Its transport formula must be credited as a specialization of the source construction. The new content is the explicit local amplitude, cancellation, boundary constant, radius, primitives in that normalization, and functional rank consequences.

## Proposed status updates

1. **Exact shift boundary:** mark the mixed spectral question about the germ at `a=-r`, exceptional nonpositive orders, and actual Taylor radius as answered. State the branch restriction and the restoration of singularity by positive spectral derivatives.
2. **Bell moment separation:** mark the specified weight-six and weight-eight elimination question as answered, with exact rational matrices. Add the general rank theorem and complete three-dimensional summation image. Keep evaluation by additional generator families open.
3. **Centered harmonic powers:** mark the complete `F_p(-2,1/2)` target in Exact Resonant Identities Question 10 as answered. Add the all-moment triangular generator and fixed-power finite Euler-sum span. A single closed bivariate generator and arithmetic minimality remain open.
4. **Generalized harmonics:** add the sufficient odd-order polynomial parity class toward Question 11. Add the all-moment formula for every single positive odd harmonic order. Do not mark the full classification, especially cancellations involving even orders, as solved.
5. **Geometric collisions:** mark the named nested digamma paths as evaluated. Extend the exact local correction to arbitrary factor count and argument-derivative orders at Stieltjes index zero. Leave positive Stieltjes indices and associative renormalized composition open.
6. **Gaussian targets:** retain the exact current `S6` and revised `S8` vectors and their conjectural status. This package supplies no proof or replacement numerical fit for them.

## Qualifications with concrete mathematical consequences

- Principal-sheet removability at early negative shifts does not imply removability on every sheet. The explicit monodromy of `D_1` around `a=-1` can introduce a pole at `a=0`.
- A polynomial formula valid at the discrete spectral label `s=-m` cannot be differentiated in `m` to infer a spectral derivative. The positive spectral jets restore logarithmic shift germs and infinite functional rank.
- The auxiliary continuation `G_m(0)=0` is not the separately specialized uncentered zeta value. The centered family has the joint regularity needed for its actual coefficient extraction.
- The entire collision counterterm is required. Repeated poles contribute rational primitive terms, and changing the geometric coordinate changes a raw constant term. The derivative example detects the omitted term explicitly.
- Bell ranks are ranks in a named formal polynomial space. Euler-sum coordinates are a proved spanning list. Neither is an assertion of arithmetic independence.
- The local collision theorem covers `gamma_0` and its argument derivatives. It does not automatically cover every generalized Stieltjes index.
- The single-harmonic-order formula is proved for positive odd order. A meromorphic restriction at an even order must not replace a separate spectral specialization without a joint-regularity check.

## Verification artifacts to retain

Retain all seven mathematical checkers in `code/`, the rational coefficient matrices in `results/bell_moments.json`, the shift and primitive check reports, the harmonic-power/generalized-harmonic output, and the collision result files. These make the signs, row conventions, test parameters, and numerical limitations reviewable.

The primary infinite identities rest on the article's analytic proofs. The exact algebraic checks certify finite formulas; the numerical records are diagnostics rather than interval certificates. A full `run_all.py` invocation creates new driver logs without being required to build the PDF.

## Further research

The article's final section contains thirteen questions with explicit targets. The most immediate are fixed-power Euler-sum coordinate matrices, one positive-Stieltjes-index nested collision, and a new Gamma generator that pairs nontrivially with the weight-six Bell annihilator.
