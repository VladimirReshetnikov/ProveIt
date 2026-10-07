# Stack Exchange polylogarithm special-value question catalog

- Created (UTC): 2026-06-02T19:36:05Z
- Repository HEAD: 3211c3f2e0494a558e30273ecdd1b4e2e1d1ef04
- Scope: questions on Math Stack Exchange and MathOverflow adjacent to `mathse-polylog-rendered-posts__71a4599d00e3.tex`
- Primary topic: symbolic evaluation of `Li_n(z)` at special points, and finite identities connecting polylogarithm values at multiple special points

## Summary

This catalog extends the five Math Stack Exchange questions already harvested into `mathse-polylog-rendered-posts__71a4599d00e3.tex`:

| Site | Question |
|---|---|
| MSE | [1424600](https://math.stackexchange.com/questions/1424600/conjecture-re-operatornameli-2-left-frac12-frac-i6-right-frac7-pi2) |
| MSE | [1430169](https://math.stackexchange.com/questions/1430169/conjectured-closed-form-for-operatornameli-2-left-sqrt2-sqrt3-cdot-e) |
| MSE | [1373123](https://math.stackexchange.com/questions/1373123/a-conjectured-identity-for-tetralogarithms-operatornameli-4) |
| MSE | [945972](https://math.stackexchange.com/questions/945972/relations-connecting-values-of-the-polylogarithm-operatornameli-n-at-ration) |
| MSE | [1579355](https://math.stackexchange.com/questions/1579355/trilogarithm-operatornameli-3z-and-the-imaginary-golden-ratio-i-phi) |

I treated a thread as a primary match when it has at least one concrete special-point polylogarithm evaluation or identity in the question body, and at least one answer with relevant mathematical content. I kept a separate bucket for open prompts whose question bodies contain usable identities but that currently have no answers. I also separated likely duplicates, low-new-information derivatives, and broad background threads.

The strongest additions found in this pass are 21 Math Stack Exchange threads and 8 MathOverflow threads. The MathOverflow set is smaller but contains several high-value dilogarithm ladder, Bloch-group, and algebraic-field identity discussions.

## Method

Inputs folded into this pass:

| Local source | Use in this report |
|---|---|
| [`report-1.tex`](report-1.tex) | Preserved its broader topic map and rechecked the concrete Stack Exchange URLs it named. One listed MSE id, `5122160`, was not visible through the current Stack Exchange API and was left unverified. |
| [`report-2.md`](report-2.md) | Used as the initial high-confidence candidate list. Two MathOverflow rows in that report now have `answer_count = 0` through the API and were reclassified as open/useful or duplicate-like prompts. |
| [`report-3.md`](report-3.md) | Used for search directions: tag pages, tag intersections, user-page harvests, and ladder/literature keywords. |
| [`report-4.txt`](report-4.txt) | All eight listed URLs were checked and placed in either the primary list or the duplicate/low-priority bucket. |

Live sources checked on 2026-06-02:

| Source | URL |
|---|---|
| MSE `polylogarithm` tag, votes sort | <https://math.stackexchange.com/questions/tagged/polylogarithm?tab=Votes> |
| MO `polylogarithms` tag, votes sort | <https://mathoverflow.net/questions/tagged/polylogarithms?tab=Votes> |
| Stack Exchange API | <https://api.stackexchange.com/docs> |

Additional API passes used `/questions/{ids}/linked`, `/questions/{ids}/related`, `/questions?tagged=...&sort=votes`, and `/search/advanced` on both `math` and `mathoverflow`. Current answer counts below are from the API payload returned during this pass.

## Primary answered matches on Math Stack Exchange

| ID | Question | Answers | Why it belongs |
|---:|---|---:|---|
| 918680 | [Closed Form for the Imaginary Part of `Li_3((1+i)/2)`](https://math.stackexchange.com/questions/918680/closed-form-for-the-imaginary-part-of-textli-3-big-frac1i2-big) | 8 | Strong complex special-point thread linking `Li_3((1+i)/2)` and `Li_3(1+i)`. From `report-2.md` and `report-4.txt`. |
| 3290798 | [A conjectured value for `Re Li_4(1+i)`](https://math.stackexchange.com/questions/3290798/a-conjectured-value-for-operatornamere-operatornameli-4-1-i) | 3 | Higher-weight analogue at the special point `1+i`; the answers contain literature-based reduction details. From `report-2.md`. |
| 3447529 | [On the relationship between `Re Li_n(1+i)` and `Li_n(1/2)` when `n >= 5`](https://math.stackexchange.com/questions/3447529/on-the-relationship-between-re-operatornameli-n1i-and-operatornameli) | 1 | Continues the `1+i` family and gives explicit known low-weight values plus a higher-weight conjectural pattern. Found through tag/API pass. |
| 676124 | [Proving a `Li_3(-1/3) - 2 Li_3(1/3)` identity](https://math.stackexchange.com/questions/676124/proving-textli-3-left-frac13-right-2-textli-3-left-frac13-rig) | 4 | Direct rational-point trilogarithm identity. From `report-2.md` and `report-4.txt`. |
| 1450917 | [A special value polylogarithm identity involving `Li_3(-1/2)`, `Li_3(-1/3)`, `Li_3(2/3)`, `Li_2(-1/3)`, `Li_2(2/3)`](https://math.stackexchange.com/questions/1450917/a-special-value-polylogarithm-identity-involving-textli-3-1-2-textli) | 1 | Composite rational-point identity mixing orders 2 and 3. From `report-2.md` and `report-4.txt`. |
| 935366 | [Simplification of an expression containing `Li_3(x)` terms](https://math.stackexchange.com/questions/935366/simplification-of-an-expression-containing-operatornameli-3x-terms) | 3 | Large finite linear combination of rational-point `Li_3` values; answers reduce it to elementary constants. Found through related/API pass. |
| 5092144 | [How to prove this `zeta(3)` form with `Li_3` and `Li_2`](https://math.stackexchange.com/questions/5092144/how-to-prove-this-zeta3-form-with-operatornameli-3-and-operatorname) | 2 | Recent rational-point mixed `Li_2`/`Li_3` identity, with answers citing named trilogarithm identities. Found through tag/API pass. |
| 463682 | [Closed form of `Li_2(phi)` and `Li_2(phi-1)`](https://math.stackexchange.com/questions/463682/closed-form-of-operatornameli-2-varphi-and-operatornameli-2-varphi-1) | 3 | Golden-ratio dilogarithm evaluations derived from classical functional equations. From `report-2.md`. |
| 1410276 | [Closed-form of `Li_2(1 +- i sqrt(3))`](https://math.stackexchange.com/questions/1410276/closed-form-of-operatornameli-2-left1-pm-i-sqrt3-right) | 3 | Complex algebraic special point; asks for real and imaginary part formulas. From `report-2.md` and `report-4.txt`. |
| 967398 | [Extract real and imaginary parts of `Li_2(i(2 +- sqrt(3)))`](https://math.stackexchange.com/questions/967398/extract-real-and-imaginary-parts-of-operatornameli-2-lefti-left2-pm-sqrt3) | 2 | Companion complex dilogarithm evaluation at quadratic algebraic points. From `report-4.txt`. |
| 1602647 | [Extract imaginary part of `Li_3(2/3 - i 2 sqrt(2)/3)` in closed form](https://math.stackexchange.com/questions/1602647/extract-imaginary-part-of-textli-3-left-frac23-i-frac2-sqrt23-ri) | 2 | Complex trilogarithm special-point evaluation; answers give reduction and generalization. From `report-4.txt`. |
| 1657298 | [How to find real part of `PolyLog[3, 1-i]` in closed form](https://math.stackexchange.com/questions/1657298/how-to-find-real-part-of-polylog3-1-i-in-closed-form) | 1 | Low-score but directly on target; the answer uses trilogarithm identities to derive a closed form. From `report-4.txt`. |
| 980179 | [Closed-form of a special value dilogarithm identity](https://math.stackexchange.com/questions/980179/closed-form-of-a-special-value-dilogarithm-identity) | 1 | Explicit finite combination of complex dilogarithm values; answer is partial but mathematically relevant. From `report-2.md`. |
| 989704 | [Closed-forms of real parts of special value dilogarithm identities from inverse tangent integral function](https://math.stackexchange.com/questions/989704/closed-forms-of-real-parts-of-special-value-dilogarithm-identities-from-inverse) | 1 | Aggregates several explicit dilogarithm combinations and real-part reductions. From `report-2.md`. |
| 1436493 | [Dilogarithm identity containing the tribonacci constant](https://math.stackexchange.com/questions/1436493/dilogarithm-identity-containing-the-tribonacci-constant) | 2 | Direct algebraic-number ladder identity for the tribonacci constant. From `report-2.md`. |
| 481682 | [Polylogarithm ladders for the tribonacci and n-nacci constants](https://math.stackexchange.com/questions/481682/polylogarithm-ladders-for-the-tribonacci-and-n-nacci-constants) | 1 | Foundational MSE ladder thread for golden, tribonacci, and n-nacci algebraic constants. From `report-2.md` and `report-1.tex`. |
| 1064100 | [Why does the tribonacci constant have a trilogarithm ladder?](https://math.stackexchange.com/questions/1064100/why-does-the-tribonacci-constant-have-a-trilogarithm-ladder) | 1 | Weight-3 ladder counterpart to the dilogarithm ladder threads; question body contains model identities. Found through tag/API pass. |
| 1959503 | [Proof of a dilogarithm identity](https://math.stackexchange.com/questions/1959503/proof-of-a-dilogarithm-identity) | 3 | Concrete two-term dilogarithm identity at quadratic algebraic arguments. Found through tag/API pass. |
| 932932 | [Known exact values of the `Li_3` function](https://math.stackexchange.com/questions/932932/known-exact-values-of-the-operatornameli-3-function) | 1 | Useful reference/list thread containing several explicit `Li_3` special values, including half and golden-ratio arguments. Found through tag/API pass. |
| 1411312 | [Closed form of a series (dilogarithm)](https://math.stackexchange.com/questions/1411312/closed-form-of-a-series-dilogarithm) | 2 | Secondary match: derives unit-circle dilogarithm real parts and Clausen-style remnants rather than a single algebraic-point identity. Found through tag/API pass. |
| 2389425 | [A very odd-looking statement about `zeta(3)` and `Li_2(1/phi^2)`](https://math.stackexchange.com/questions/2389425/a-very-odd-looking-statement-about-zeta3-and-textli-2-left-frac1-va) | 3 | Secondary golden-ratio identity thread tying a known dilogarithm value to a `zeta(3)` expression. Found through tag/API pass. |

## Primary answered matches on MathOverflow

| ID | Question | Answers | Why it belongs |
|---:|---|---:|---|
| 492746 | [Proving identity involving dilogarithms and `pi/9`](https://mathoverflow.net/questions/492746/proving-identity-involving-dilogarithms-and-pi-9) | 3 | Concrete algebraic/root-of-unity dilogarithm identity, with answers pointing to Kirillov-style families. Found through MO tag/API pass. |
| 85986 | [A dilogarithm identity: known or new?](https://mathoverflow.net/questions/85986/a-dilogarithm-identity-known-or-new) | 3 | Parameterized dilogarithm identity; answers reduce it using classical two- and five-term relations. Found through MO tag/API pass. |
| 144322 | [The relationship between the dilogarithm and the golden ratio](https://mathoverflow.net/questions/144322/the-relationship-between-the-dilogarithm-and-the-golden-ratio) | 4 | Golden-ratio `Li_2` identities and their Bloch-group/five-term background. Found through MO tag/API pass. |
| 261408 | [Several conjectured identities for polylogarithms](https://mathoverflow.net/questions/261408/several-conjectured-identities-for-polylogarithms) | 1 | Cross-post/extension of the archived MSE tetralogarithm direction, but it adds higher-weight golden-ratio identities and a useful literature answer. Found through MO tag/API pass. |
| 450252 | [An identity involving polylogarithms](https://mathoverflow.net/questions/450252/an-identity-involving-polylogarithms) | 3 | Explicit complex dilogarithm identity involving a quadratic imaginary field; answers derive it by standard dilog transforms. Found through MO tag/API pass. |
| 511718 | [Two-term dilogarithmic identity simplification](https://mathoverflow.net/questions/511718/two-term-dilogarithmic-identity-simplification) | 1 | Recent two-term golden-ratio dilogarithm identity; answer reduces the polylogarithms away and analyzes the residual algebra. Found through MO tag/API pass. |
| 511765 | [Daniel Shanks "simplest cubic fields" and dilogarithm identities](https://mathoverflow.net/questions/511765/daniel-shanks-simplest-cubic-fields-and-dilogarithm-identities) | 1 | Recent cubic-field/Rogers-dilogarithm identity thread with relevant accepted answer. Found through MO tag/API pass. |
| 131111 | [Is this combination of generalized polygamma and dilogarithm actually zero?](https://mathoverflow.net/questions/131111/is-this-combination-of-generalized-polygamma-and-dilogarithm-actually-zero-im) | 3 | Borderline but relevant: special-value identity involving `Li_2(e^{-2 pi})`, with answers adding related conjectural reductions. Found through MO tag/API pass. |

## Open prompts with usable identity examples but no meaningful answers

These threads currently have `answer_count = 0` through the Stack Exchange API, but their question bodies contain enough explicit polylogarithmic structure to be useful as future harvest leads.

| Site | ID | Question | Why it remains useful |
|---|---:|---|---|
| MSE | 5080786 | [Ramanujan type formulas for polylogarithm](https://math.stackexchange.com/questions/5080786/ramanujan-type-formulas-for-polylogarithm) | Gives explicit formula families for `Li_{2k}` and `Li_{2k-1}` at roots of unity; no answer yet. |
| MSE | 5023055 | [How to find closed form for a complex expression involving special functions and polylogarithms?](https://math.stackexchange.com/questions/5023055/how-to-find-closed-form-for-a-complex-expression-involving-special-functions-and) | Contains a concrete identity involving `Im Li_2((-1+i)/2)` and Lerch transcendent terms; no answer yet. |
| MO | 173492 | [Dilogarithm of -1/2?](https://mathoverflow.net/questions/173492/dilogarithm-of-1-2) | Open elementary-reducibility question for `Li_2(-1/2)`, with a comparison to Euler's `Li_2(1/2)` value. |
| MO | 141185 | [A second polylogarithm ladder for the tribonacci and n-nacci constants](https://mathoverflow.net/questions/141185/a-second-polylogarithm-ladder-for-the-tribonacci-and-n-nacci-constants) | Contains a Bailey-Broadhurst ladder example, but no answers. It is also duplicate-like relative to MSE ladder threads. |
| MO | 490573 | [The imaginary part of two-term complex dilogarithms](https://mathoverflow.net/questions/490573/the-imaginary-part-of-two-term-complex-dilogarithms) | Contains explicit two-term complex dilogarithm identities, but no answers. This corrects the stale nonzero-answer classification in `report-2.md`. |
| MO | 496682 | [Deriving a 4-term functional dilogarithm identity by Kirillov](https://mathoverflow.net/questions/496682/deriving-a-4-term-functional-dilogarithm-identity-by-kirillov) | Functional-equation rather than special-point focused, but the explicit Kirillov identity makes it a useful nearby lead. No answers. |

## Duplicate-like or low-new-information threads

These are not useless, but I would not prioritize them ahead of the primary list because they appear to add little new relevant information.

| Site | ID | Question | Classification |
|---|---:|---|---|
| MSE | 3938336 | [Evaluate a series equal to `Li_3((3-sqrt(5))/2)`](https://math.stackexchange.com/questions/3938336/evaluate-sum-limits-n-1-infty-frac-left-frac3-sqrt52-right) | Answered, but essentially a request for the known `Li_3(phi^{-2})` value. It belongs below `932932` and the golden-ratio threads. From `report-4.txt`. |
| MO | 141185 | [A second polylogarithm ladder for the tribonacci and n-nacci constants](https://mathoverflow.net/questions/141185/a-second-polylogarithm-ladder-for-the-tribonacci-and-n-nacci-constants) | No answers and likely a MathOverflow counterpart to the richer MSE ladder material at `481682` and `1064100`. |
| MO | 261408 | [Several conjectured identities for polylogarithms](https://mathoverflow.net/questions/261408/several-conjectured-identities-for-polylogarithms) | Cross-post/extension of an archived MSE direction. It remains in the primary MO list because it adds higher-weight identities and a literature answer. |

## Rejected or parked: no answer and no special-value identity example

The following search hits were segregated because they currently have no meaningful answers and do not contain an explicit special-point evaluation or finite identity of the target kind in the question body. Some are mathematically interesting, but they are not useful as immediate source markup for a special-value identity corpus.

| Site | ID | Question | Reason parked |
|---|---:|---|---|
| MSE | 5110303 | [Does the polylogarithm `Li_k(x)` solve a first or second order ODE/ADE?](https://math.stackexchange.com/questions/5110303/does-the-polylogarithm-mathrmli-kx-solve-a-first-or-second-order-ode-ade) | General differential-equation question, no answer, no special-point identity. |
| MSE | 5127863 | [Completing proof of formula for a hard polylogarithmic integral](https://math.stackexchange.com/questions/5127863/completing-proof-of-formula-for-a-hard-polylogarithmic-integral) | No answer; contains a Lewin integral formula, but not a special-point evaluation thread. |
| MSE | 4986171 | [Understanding polylogarithm branch points, monodromy and multivaluedness](https://math.stackexchange.com/questions/4986171/understanding-polylogarithms-branch-points-monodromy-and-multivaluedness-espec) | General analytic-continuation question, no answer, no identity example of the target kind. |
| MO | 85774 | [Is the quantum dilogarithm related in any way to cohomology of quantum groups?](https://mathoverflow.net/questions/85774/is-the-quantum-dilogarithm-related-in-any-way-to-cohomology-of-quantum-groups) | Broad conceptual quantum-dilogarithm prompt, no answers, not a special-point evaluation. |
| MO | 160646 | [Inverse of polylogarithm](https://mathoverflow.net/questions/160646/inverse-of-polylogarithm) | No answer; not about special values or identities. |
| MO | 333610 | [Limiting property of polylogarithm ratio](https://mathoverflow.net/questions/333610/limiting-property-of-polylogarithm-ratio) | No answer; asymptotic/ratio question, not a special-point identity. |
| MO | 279588 | [Approximations of polylogarithm and Lerch transcendent?](https://mathoverflow.net/questions/279588/approximations-of-polylogarithm-and-lerch-transcendent) | No answer; approximation question, no target identity. |
| MO | 218158 | [Root polylogarithm dominance questions](https://mathoverflow.net/questions/218158/root-polylogarithm-dominance-questions) | No answer; dominance/partition-root context, not symbolic special-value evaluation. |

## Near misses and background threads

These are adjacent enough to keep as references, especially for proof techniques or context, but they are not primary source questions for the requested identity corpus.

| Site | ID | Question | Why not primary |
|---|---:|---|---|
| MSE | 1210644 | [Proving a `sum cos(n)/n^4` evaluation](https://math.stackexchange.com/questions/1210644/proving-sum-n-1-infty-frac-cosnn4-frac-pi-490-frac-pi-2) | Equivalent to `Re Li_4(e^i)`, but framed as a Fourier-series evaluation at a nonalgebraic unit-circle point. |
| MSE | 376180 | [Integral identity involving `Li_2(-1-e^{ix})`](https://math.stackexchange.com/questions/376180/identity-i-int-0-pi-left-mathrmli-2-left-1-eix-right-mathrmli-2-l) | Polylogarithm-valued integral identity rather than finite special-point evaluation. |
| MSE | 4284361 | [Closed form evaluation of a trigonometric integral in terms of polylogarithms](https://math.stackexchange.com/questions/4284361/closed-form-evaluation-of-a-trigonometric-integral-in-terms-of-polylogarithms) | Integral evaluation whose answer contains polylogs; not primarily a polylog special-value identity. Listed in `report-1.tex`. |
| MSE | 5125161 | [Verify a polylogarithmic evaluation of a 5D integral over a positive orthant](https://math.stackexchange.com/questions/5125161/verify-a-polylogarithmic-evaluation-of-a-5d-integral-over-0-infty5) | The question uses a rational-point polylog identity inside an integral verification, but the thread is not centered on discovering or proving that identity. Listed in `report-1.tex`. |
| MO | 347747 | [Simplify the difference of two dilogarithms](https://mathoverflow.net/questions/347747/simplify-the-difference-of-two-dilogarithms-as-in-the-logarithmic-counterpart) | Relevant negative-evidence thread: asks for simplification, answers indicate little elementary collapse is expected. |
| MO | 2402 | [Abel's equation for the dilog](https://mathoverflow.net/questions/2402/abels-equation-for-the-dilog) | Important functional-equation background, not a special-point evaluation catalog item. |
| MO | 25428 | [What is special about polylogarithms that leads to so many interesting identities and applications?](https://mathoverflow.net/questions/25428/what-is-special-about-polylogarithms-that-leads-to-so-many-interesting-identitie) | Good conceptual background, no concrete target identity corpus. Listed in `report-1.tex` and `report-3.md`. |
| MO | 242920 | [Polylogarithm sheaves](https://mathoverflow.net/questions/242920/polylogarithm-sheaves) | Algebraic-geometry background rather than symbolic evaluation at special points. Listed in `report-1.tex`. |
| MO | 309945 | [A remarkable almost-identity](https://mathoverflow.net/questions/309945/a-remarkable-almost-identity) | Interesting polylog-adjacent numerical phenomenon, but not a special-point `Li_n` identity thread of the requested kind. |

## Further search directions

The most productive next pass would be a deeper manual/API walk of:

| Direction | Notes |
|---|---|
| MSE tag intersections | `polylogarithm` + `closed-form`, `conjectures`, `experimental-mathematics`, `special-functions`, and possible synonym searches for `dilogarithm`, `trilogarithm`, `Clausen`, `Glaisher`, and `inverse tangent integral`. |
| MathOverflow tag intersections | `polylogarithms` with `nt.number-theory`, `ag.algebraic-geometry`, `kt.k-theory-homology`, `multiple-zeta-values`, `hyperbolic-geometry`, and `motives`. |
| User-page harvests | The preliminary report correctly flags Vladimir Reshetnikov's MSE question list as a dense source. Other productive names from the MSE `polylogarithm` tag include Cleo, Olivier Oloa, Tito Piezas III, Jack D'Aurizio, Yuriy S, Iaroslav Blagouchine, Robert Israel, achille hui, Lucian, Anastasiya-Romanova, M.N.C.E., and nospoon. |
| Ladder keywords | `polylogarithm ladder`, `Lewin`, `Cohen Lewin Zagier`, `Abouzahra`, `Bailey Broadhurst`, `Kirillov`, `Rogers dilogarithm`, `Bloch group`, `tribonacci`, `plastic constant`, `Salem number`, and `Lehmer polynomial`. |
| Half-argument and rational-point families | Search explicit strings such as `Li_4(1/2)`, `Li_5(1/2)`, `Li_3(1/3)`, `Li_3(-1/3)`, `Li_n rational points`, and `Zagier polylogarithm rational`. Many hits are broad or unproved, so they should be screened against the same explicit-identity and meaningful-answer criteria. |

## Current high-value harvest set

For a source-markup/PDF follow-up similar to `mathse-polylog-rendered-posts__71a4599d00e3.tex`, I would start with these 29 answered threads:

- MSE: 918680, 3290798, 3447529, 676124, 1450917, 935366, 5092144, 463682, 1410276, 967398, 1602647, 1657298, 980179, 989704, 1436493, 481682, 1064100, 1959503, 932932, 1411312, 2389425.
- MO: 492746, 85986, 144322, 261408, 450252, 511718, 511765, 131111.

The open-but-useful prompts worth monitoring are MSE 5080786, MSE 5023055, MO 173492, MO 141185, MO 490573, and MO 496682.
