# Stack Exchange polygamma special-value question catalog

- Created (UTC): 2026-06-02T23:17:56Z
- Repository HEAD: 33631d91f62bc7ef4dcb02eb91b62f0e07fe4694
- Scope: questions on Math Stack Exchange and MathOverflow analogous to the polylogarithm special-value catalog, but for polygamma, digamma, trigamma, and negative-order generalized polygamma values
- Seed questions:
  - <https://math.stackexchange.com/questions/897967/trigamma-identity-4-psi-1-left-frac15-right-psi-1-left-frac25-right>
  - <https://math.stackexchange.com/questions/893486/looking-for-an-identity-connecting-polylogarithm-and-polygamma-functions-of-argu>

## Inclusion rule

I treated a thread as a primary match when the question body itself asks about a concrete special-value identity, finite relation, or named-function bridge involving polygamma values. This includes ordinary positive-order polygamma values, digamma/trigamma special values, and negative or generalized orders such as `\psi^{(-2)}`. I kept integral or series questions in a separate bucket when the polygamma content appears mainly as an evaluation tool rather than as the main object of the question.

## Search method

The search combined:

| Source | Queries or endpoints |
| --- | --- |
| Stack Exchange API `search/advanced` | `polygamma identity`, `PolyGamma identity`, `trigamma identity`, `digamma identity`, `polygamma values`, `negative order polygamma`, `PolyGamma[-1`, `PolyGamma[-2`, `polygamma polylogarithm`, `digamma polylogarithm`, `Hurwitz zeta polygamma`, `Lerch polygamma`, `Catalan polygamma`, `reflection formula polygamma`, `multiplication formula polygamma`, and variants |
| Stack Exchange API question graph | `linked` and `related` for MSE `897967`, MSE `893486`, and MO `131111` |
| Tag harvest | MSE `polygamma`, `digamma-function`, `polylogarithm;polygamma`, `closed-form;polygamma`; MO `poly-gamma-function`, `gamma-function`, `closed-form-expressions` |
| Web cross-check | targeted `site:math.stackexchange.com` / `site:mathoverflow.net` searches for `trigamma identity`, `psi^{(-2)}`, `negative order polygamma`, `Lerch`, `PolyGamma`, and rational-argument combinations |

## Primary answered matches on Math Stack Exchange

| ID | Question | Answers | Why it matches |
| --- | --- | ---: | --- |
| 897967 | [Trigamma identity `4 psi_1(1/5)+psi_1(2/5)-psi_1(1/10)=4 pi^2/(phi sqrt(5))`](https://math.stackexchange.com/questions/897967/trigamma-identity-4-psi-1-left-frac15-right-psi-1-left-frac25-right) | 2 | Seed thread. Direct finite trigamma identity at rational arguments; answer proves it via reflection and multiplication. |
| 4290297 | [New trigamma identity for `Psi_1(3/20)+6 Psi_1(1/5)+10 Psi_1(2/5)-Psi_1(1/20)`](https://math.stackexchange.com/questions/4290297/new-trigamma-identity-for-psi-1-frac3206-psi-1-frac1510-psi-1-fra) | 1 | Linked from `897967`. Same finite-trigamma-lattice theme, denominator `20`, with Catalan and algebraic multiples of `pi^2`. |
| 953976 | [Prove `psi^(1)(5/6)-psi^(1)(1/6)=5(psi^(1)(2/3)-psi^(1)(1/3))`](https://math.stackexchange.com/questions/953976/prove-psi1-left-frac-56-right-psi1-left-frac-16-right-5-left) | 1 | Direct rational-argument trigamma relation. |
| 2802872 | [Trigamma identity `psi_1(11/12)-psi_1(5/12)=4 sqrt(3) pi^2-80G`](https://math.stackexchange.com/questions/2802872/trigamma-identity-psi-1-left-frac1112-right-psi-1-left-frac512-rig) | 3 | Direct rational-argument trigamma identity with Catalan's constant. |
| 3063097 | [Alternative proof for `zeta(2,1/4)=psi^(1)(1/4)=pi^2+8G`](https://math.stackexchange.com/questions/3063097/alternative-proof-for-zeta-left2-frac14-right-psi1-left-frac14-right) | 3 | Special value of trigamma/Hurwitz zeta at `1/4`; the thread asks for alternate proof machinery. |
| 2952474 | [Is it possible to simplify `psi^(2)(1/8)` or `psi^(2)(p/q)`?](https://math.stackexchange.com/questions/2952474/is-it-possible-to-simplify-psi2-frac18-or-psi2-frac-pq) | 2 | Direct higher-order polygamma special-value question at rational arguments, including examples at denominators `2,3,4,6`. |
| 4040435 | [General summation formula for `psi^(s)(1/2)`, including negative orders](https://math.stackexchange.com/questions/4040435/is-there-a-general-summation-formula-for-the-polygamma-function-at-z-1-2-i-e) | 1 | Direct special-value thread at `1/2`; explicitly contrasts positive-order zeta formulas with `psi^(-1)`, `psi^(-2)`, and `psi^(-3)` values. |
| 4784920 | [Closed form for `psi^(-2)(1/4)`](https://math.stackexchange.com/questions/4784920/closed-form-for-psi-2-left-frac14-right) | 1 | Direct negative-order polygamma special value involving Glaisher-Kinkelin and Catalan constants. |
| 893486 | [Identity connecting polylogarithm and polygamma functions of arguments `1/4` and `3/4`](https://math.stackexchange.com/questions/893486/looking-for-an-identity-connecting-polylogarithm-and-polygamma-functions-of-argu) | 1 | Seed thread. The answer reconstructs a bridge between `psi^(n)(3/4)-psi^(n)(1/4)` and `Im Li_{n+1}(i)`. |
| 4504218 | [Identity relating the polygamma function and the Lerch transcendent](https://math.stackexchange.com/questions/4504218/can-somebody-show-me-how-to-derive-the-identity-relating-the-polygamma-function) | 1 | Explicit bridge between `Phi(-1,m+1,z)` and a half-argument difference of `psi^(m)`. |
| 3653746 | [Decomposition of `psi^(n)(1)` in terms of `psi^(n)(k)`](https://math.stackexchange.com/questions/3653746/decomposition-of-psin1-in-terms-of-psink) | 2 | Infinite but explicit identity family relating one special value to a signed sum over integer arguments. |
| 1154373 | [An identity on Polygamma](https://math.stackexchange.com/questions/1154373/an-identity-on-polygamma) | 1 | Basic but direct derivation of the defining series for `psi^(n)(z)`; useful as a proof primitive for many rational-argument identities. |
| 597867 | [Multiplication formula for the Hurwitz zeta function](https://math.stackexchange.com/questions/597867/the-multiplication-formula-for-the-hurwitz-zeta-function) | 1 | Hurwitz-zeta multiplication formula; the question explicitly notes the induced multiplication formula for positive-order polygamma. |
| 1335002 | [An infinite series in polygamma function](https://math.stackexchange.com/questions/1335002/an-infinite-series-in-polygamma-function) | 2 | Negative-order polygamma series with conjectured closed forms involving `log A`, `gamma`, `zeta(2)`, `zeta(3)`, and zeta derivatives. |
| 4441095 | [Closed form for a derivative limit involving `psi^(0)` and higher polygamma values at `1`](https://math.stackexchange.com/questions/4441095/closed-form-for-lim-m-to-0-frac-partial2a-1-partial-m2a-1-pi-csc) | 1 | Pattern identity expressing a family of derivative limits through finite sums of `eta(2k) psi^(2a-2k)(1)`. |

## Primary answered matches on MathOverflow

| ID | Question | Answers | Why it matches |
| --- | --- | ---: | --- |
| 131111 | [Is this combination of generalized polygamma and dilogarithm actually zero?](https://mathoverflow.net/questions/131111/is-this-combination-of-generalized-polygamma-and-dilogarithm-actually-zero-im) | 3 | Strongest MO match. Direct negative-order identity involving `Im psi^(-2)(1+i)` and `Li_2(e^{-2 pi})`; answers give a one-parameter generalization. |
| 312479 | [`pi` in terms of polygamma](https://mathoverflow.net/questions/312479/pi-in-terms-of-polygamma) | 1 | Direct experimental identity `pi^2 = (15 psi(1,1/3)-3 psi(1,1/6))/4`. |
| 312550 | [`psi(2,1/6)`, `psi(4,1/6)` in terms of zeta and pi only](https://mathoverflow.net/questions/312550/psi2-1-6-psi4-1-6-in-terms-of-zeta-and-pi-only-and-another-closed-form-f) | 1 | Higher-order rational-argument polygamma values, with explicit formulas and a generalization question. |
| 42696 | [Connection between Bernoulli polynomials and polygamma function](https://mathoverflow.net/questions/42696/connection-between-bernoulli-polynomials-and-polygamma-function) | 1 | Generalized/balanced polygamma relation to Hurwitz zeta and Bernoulli polynomials; answered on MO. This is essentially the answered counterpart to MSE `7183`. |
| 347520 | [Reference request: sums of rational functions and polygamma functions](https://mathoverflow.net/questions/347520/reference-request-sums-of-rational-functions-and-polygamma-functions) | 1 | Reference-style but directly asks for the rational-function-sum-to-polygamma reduction literature. |
| 251727 | [Closed form for sum involving digamma?](https://mathoverflow.net/questions/251727/closed-form-for-sum-involving-digamma) | 1 | Lower-signal, but it asks about a closed form for a sum over integer digamma values. |

## Open or no-meaningful-answer leads

These are worth retaining as leads, but they should not be mixed into an answered harvest without an explicit "open" marker.

| Site | ID | Question | Answers | Note |
| --- | --- | --- | ---: | --- |
| MSE | 1909595 | [Interesting connection between polylogarithms and polygamma functions](https://math.stackexchange.com/questions/1909595/interesting-connection-between-polylogarithms-and-polygamma-functions) | 0 | Concrete `Li_q(-1)` / polygamma-at-`1/2` identity family in the question body; no answers. |
| MSE | 4319642 | [Simplification of a difficult identity involving the digamma function](https://math.stackexchange.com/questions/4319642/simplification-of-a-difficult-identity-involving-the-digamma-function) | 0 | Substantial digamma/cotangent-sum manipulation, but no posted answer. |
| MSE | 3555737 | [Sum involving 2nd antiderivative of the digamma function](https://math.stackexchange.com/questions/3555737/sum-involving-2nd-antiderivative-of-the-digamma-function) | 0 | Explicit series with `psi^(-2)` values and a conjectured transformed form; no answers. |
| MSE | 7183 | [Connection between Bernoulli polynomials and polygamma function](https://math.stackexchange.com/questions/7183/connection-between-bernoulli-polynomials-and-polygamma-function) | 0 | Same question as MO `42696`; keep as duplicate/open MSE copy. |
| MSE | 521203 | [Recurrence relation for polygamma reflection polynomials](https://math.stackexchange.com/questions/521203/recurrence-relation-for-polygamma-reflection-polynomials) | 0 | Structural reflection-formula thread; no answers. |
| MSE | 4845364 | [Closed form for `psi^(1/k)(1)`, where `k` is an integer](https://math.stackexchange.com/questions/4845364/closed-form-for-psi1-k1-where-k-is-an-integer) | 0 | Fractional-order rather than negative-order, but topically close to generalized polygamma closed forms. |
| MO | 152299 | [Recurrence formula for digamma function with rational number](https://mathoverflow.net/questions/152299/recurrence-formula-for-digamma-function-with-rational-number) | 0 | Rational-shift digamma recurrence question; no answers. |
| MO | 372726 | [Can a digamma generating-function expression be simplified?](https://mathoverflow.net/questions/372726/can-x-sum-k-1-infty-frac1k-big-gamma-psi-big1-fracx) | 0 | Digamma appears in a zeta-generating-function simplification problem; no answers. |
| MO | 455136 | [Negativity of a determinant involving trigamma, tetragamma, and pentagamma](https://mathoverflow.net/questions/455136/how-to-prove-negativity-of-a-3-times3-determinant-whose-elements-involve-triga) | 0 | Polygamma determinant inequality, not a special-value identity; no answers. |

## Adjacent answered leads

These threads are not primarily about identities among named polygamma values, but their questions or answers contain reusable polygamma special-value reductions.

| Site | ID | Question | Answers | Note |
| --- | --- | --- | ---: | --- |
| MSE | 1427206 | [Conjecture for an integral involving `psi^(1)(1/3)`](https://math.stackexchange.com/questions/1427206/conjecture-int-01-frac-ln2-left1xx2-rightx-dx-stackrel-frac2-pi9) | 2 | Polylog/polygamma overlap: the question states a compact integral value involving `psi^(1)(1/3)` and notes equivalent dilogarithmic forms. |
| MSE | 1430169 | [Conjectured closed form for a complex dilogarithm value](https://math.stackexchange.com/questions/1430169/conjectured-closed-form-for-operatornameli-2-left-sqrt2-sqrt3-cdot-e) | 3 | Primarily a dilogarithm thread, but the proposed imaginary part contains `psi^(1)(1/3)`. Already harvested in the polylog document. |
| MSE | 1346396 | [Logarithmic Integral I](https://math.stackexchange.com/questions/1346396/logarithmic-integral-i) | 1 | Integral conjecture whose proposed value contains `psi^(1)(1/3)+psi^(1)(1/6)`. |
| MSE | 3075324 | [Improper integral with trigamma identity in the solution path](https://math.stackexchange.com/questions/3075324/improper-integral-int-limits-0-infty-frac-x2-arctan-x-x4-x2-1) | 3 | Not a polygamma question, but an answer uses trigamma identities at twelfths. |
| MSE | 4634827 | [Closed form for a fractional-part integral](https://math.stackexchange.com/questions/4634827/closed-form-for-int-01-left-fracmx-right-n-dx) | 2 | Answer expresses the integral using negative-order polygamma differences. |
| MSE | 2683542 | [Meaning and definition of `psi^(-2)(x)`](https://math.stackexchange.com/questions/2683542/the-meaning-and-definition-of-psi-2x-and-the-convergence-of-some-rela) | 1 | Definition/background for negative-order polygamma plus Mobius-weighted series questions. |
| MSE | 5080998 | [Integral of a trigamma difference at conjugate half-line arguments](https://math.stackexchange.com/questions/5080998/int-0-infty-frac-psi1-left-tfrac1-i-u2-right-psi1-left) | 2 | Integral evaluation involving `psi^(1)((1\pm iu)/2)` rather than fixed special values. |
| MO | 220759 | [Closed form for `sum 1/(1+n+...+n^a)`](https://mathoverflow.net/questions/220759/closed-form-for-sum-n-1-infty-frac11nn2-cdotsna) | 2 | General series whose low-parameter cases are expressed through digamma/polygamma. |
| MO | 378665 | [Closed form of `sum_{r>=2} zeta(r)/r^2`](https://mathoverflow.net/questions/378665/closed-form-of-the-sum-sum-r-ge2-frac-zetarr2) | 0 | Open MO lead; included here because the body connects a zeta sum, a digamma integral, and a limiting polylogarithm expression. |

## Useful next harvest order

1. Start with the six strongest finite trigamma/rational-argument MSE threads: `897967`, `4290297`, `953976`, `2802872`, `3063097`, and `2952474`.
2. Add the negative-order bridge threads: MSE `4784920`, MSE `4040435`, MSE `1335002`, and MO `131111`.
3. Add the special-function bridge threads: MSE `893486`, MSE `4504218`, MO `312479`, MO `312550`, and MO `42696`.
4. Keep the open/no-answer leads separate; several contain explicit identity examples, but they should not be represented as solved threads.
