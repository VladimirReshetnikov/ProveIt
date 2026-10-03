# Safe endpoint penalties after three-mass selector projection

The two reviewed transformations can be composed by grouping each endpoint penalty with the selector barrier at its step. This gives complete paid circuits of **46 / 45 operations** for the two-step native / compact-clean examples, and **86 / 83** for the three-increment examples. These improve the projected parent circuits' 47 / 46 and 91 / 88 operations. The respective witness counts remain six and fifteen, and the degree remains exactly three.

The [portable checker/emitter](three_mass_projected_endpoint_penalties.py) authenticates both [endpoint-penalty](three_mass_endpoint_penalties.md) and [selector-projection](three_mass_selector_projection.md) sources before execution. The [receipt](three_mass_projected_endpoint_penalties.json) includes complete best circuits, all tested ledgers, source certificates, exact polynomial comparisons, and the one-step counterfeit explaining the necessary guard.

## The grouped nonnegativity proof

At one projected step, keep the explicit natural selectors `e_j` and masses `v_j`, and restore the implicit selector by

\[
S=\sum_{j\ne *}e_j,\qquad e_*=1-S.
\]

The parent selector gadget is

\[
G=S(S-1)+\sum_{j\ne *}(1-e_j)^2v_j+Sv_*.
\]

Let any selected subset of the initial/terminal endpoint squares be replaced by the corresponding forbidden-branch penalty `K`. If its implicit branch is allowed, its projected penalty is a sum of explicit natural selectors and is nonnegative. If the implicit branch is forbidden, then

\[
K=1-A,\qquad A=\sum_{\text{explicit allowed }j}e_j\le S.
\]

Let `r` be the number of attached endpoint penalties whose implicit branch is forbidden. There are at most two. Set

\[
w=\begin{cases}2&r=2,\\1&r=0\text{ or }1,\end{cases}
\qquad
G_w=wS(S-1)+\sum_{j\ne *}(1-e_j)^2v_j+Sv_*.
\]

For every natural tuple with `S>=2`, the grouped step expression satisfies

\[
G_w+\sum K\ \ge\ wS(S-1)+r(1-S)
 =(S-1)(wS-r)>0.
\]

For `S=0` or `1`, the explicit selectors and restored implicit selector are natural and one-hot. Every attached penalty is then a nonnegative forbidden-selection indicator; every other gadget summand is nonnegative. Thus the grouped expression is nonnegative on the entire supplied natural orthant and is zero exactly when the restored selector is one-hot, every inactive mass is zero, and each attached endpoint condition holds.

For `h>=2`, initial and terminal penalties attach to different steps, so `r<=1` and **no extra barrier arithmetic** is required. For `h=1`, both can attach to the same step. Only when both contain the implicit branch is the original barrier doubled. The literal emitter charges that doubling by an addition. It also emits the alternatives of replacing only the initial or only the terminal endpoint, permitting a fair choice when replacing both costs more.

All retained affine squares are nonnegative. Grouping the global sum by step therefore proves that a complete new natural zero restores a zero of the original mass-coordinate certificate. Conversely an original natural zero projects to a new one: `S` is zero or one, the added barrier vanishes, and the endpoint predicates agree. The coordinate projection and unique restoration `e_*=1-S` are inverse on complete natural zero fibers. The ordinary raw loader `N0=x+1`, mass/value and internal control equations, native `y,T` or compact cleaned `T`, and every remaining witness are still paid.

For `h=0` no endpoint square is replaced. For `B=0,h>0` the retained impossible one-hot square prevents every zero. There is no positive-fiber or same-coordinate equivalence outside the natural witness domain.

## Why the one-step guard is necessary

Use actual producer states `(s,h,z)`, halt `h`, and instructions `s -> h` testing zero of the prime-three counter, together with `z -> z` no-op. The producer expands the zero test into the two nonzero residue branches; make the no-op branch implicit. At horizon one supply

\[
x=2,\quad(e_0,e_1)=(1,1),\quad(v_0,v_1,v_*)=(1,1,0),
\quad y=3,\quad T=584.
\]

The restored implicit selector is `-1`. Both projected endpoint penalties equal `-1`, canceling the original barrier `S(S-1)=2`. The value, output and time squares vanish, so the **unguarded combined full polynomial is zero**. Yet raw `N0=3` fails the intended prime-three zero guard. The unchanged projected parent scores seven; the safely combined polynomial, with barrier weight two, scores two. The receipt evaluates these exact complete circuits and records the actual branch table and assignment. This is not merely a hypothetical local inequality failure.

## Entire-polynomial correction and costs

Let `H` be the projected parent polynomial and `rho` its affine selector restoration. For the replaced endpoint subset `A`, the new complete polynomial is

\[
H_{\rm end}=H-
 \sum_{a\in A}(C_a\circ\rho)^2+
 \sum_{a\in A}K_a\circ\rho+
 \sum_t(w_t-1)S_t(S_t-1).
\]

This is an exact all-value polynomial identity with a displayed correction. Neither off-zero equality with the parent nor arbitrary-integer zero equivalence is asserted. Combining it with the parent's already proved substitution correction gives the complete relation to the original mass polynomial.

The old schedule is the actual projected emitter: with no endpoint replacement, every emitted row, output and ledger is checked literally identical. For each actual certificate, both old and new comparisons enumerate every **uniform implicit-branch choice** and the same direct/factored/Horner gadget schedules. The new side additionally considers initial, terminal, or both endpoint replacements. This is a finite set of emitted schedules, not global optimality or an exhaustive search over varying per-step choices. The general API also accepts the parent's per-step implicit-index list, but the reported comparison family is the stated uniform one.

| Fixture | Endpoints | Projected parent | Safely combined | Witnesses | Best replacement |
|---|---|---:|---:|---:|---|
| `INC2; DEC2`, `B=h=2` | Native `y,T` | 18M+29A=47 | 17M+29A=46 | 6 | Initial |
| Same | Compact cleaned `T` | 19M+27A=46 | 18M+27A=45 | 6 | Initial |
| Three `INC2`, `B=h=3` | Native `y,T` | 28M+63A=91 | 26M+60A=86 | 15 | Both |
| Same | Compact cleaned `T` | 28M+60A=88 | 26M+57A=83 | 15 | Both |
| Prime-three zero test, `B=2,h=1` | Native `y,T` | 9M+15A=24 | 9M+15A=24 | 3 | No improvement |
| Already halted, `B=h=0` | Compact cleaned `T` | 2M+3A=5 | 2M+3A=5 | 0 | Unchanged |

All input, affine endpoint, selector, complementarity, squaring and final-accumulation arithmetic is in the literal sources. The metrics charge fixed nonunit coefficients and fold only the same constant/unit cases as the reviewed parent. The best worked two-step form replaces only one endpoint because retaining a shared projected square is cheaper than compiling both linear penalties.

For `B>=2,h>=1`, a surviving explicit monomial `e_j^2 v_j` has coefficient one; all other changed terms have degree at most two. Hence degree is exactly three. In the other supported cases, the unchanged `T^2` term gives exact degree two. All emitted degrees are checked from full coefficient expansions.

## Evidence, pins and limits

The authenticated sibling source pins are:

- `three_mass_endpoint_penalties.py`: `7010ab32c2ac44a84ea61f4393b826cdc1401c654f20364dbad7f694e3eb605c`.
- `three_mass_selector_projection.py`: `8129ec4da0aded05c98993b7575eb3ccfe42ee908c5d15c18a748a8b53d874b8`.

The endpoint helper loads the committed base `three_mass_arithmetic.py` by pinned immutable Git blob, then authenticates both original archives and their producer modules before execution. No warm bytecode or repository module import is trusted. Only private module namespaces and temporary producer modules are used; no author suite is rerun.

The receipt records 261 literal projected-baseline comparisons, 783 whole-coefficient correction and degree checks, 1,566 signed full-output corrections, and 882 actual natural-zero forward lifts. An independent direct formula census covers 270,600 natural gadget tuples with arbitrary pairs of forbidden-support masks, including the one-step overlap. Another 2,889 complete natural tuples check full nonnegativity and six inverse zero restorations. These are explicitly bounded checks; the grouped inequality supplies the general theorem.

```sh
python three_mass_projected_endpoint_penalties.py \
  --root /path/to/directory/containing/the/two/pinned/helpers \
  --repo /path/to/Proofs \
  --expect three_mass_projected_endpoint_penalties.json
```

`--root` defaults to this script's directory. `--output PATH` writes the deterministic receipt; comparisons retain exact Python types. A fresh replay matched the saved receipt. No repository or archive is modified.

This remains a compiler for an externally fixed horizon and the reviewed paid raw source input. No uniform unbounded-history representation, universal fixed branch table, ordinary-counter decoder, fixed-arity universal equation, or new universal operation bound is claimed. The degree-two endpoint-only construction remains a separate tradeoff with more witnesses.

The [independent full-source review](review_three_mass_projected_endpoint_penalties.md)
reconstructs all 783 candidate coefficient polynomials and exact degrees,
261 literal baselines and 56,077 live paid gates. It also checks 36 additional
mixed-index/scaled-clock forms, every omitted position in a 14,216-case local
mask census, and 2,889 complete natural tuples. The actual one-step false zero
is independently reproduced and rejected. Root read both complete sources and
notes and freshly replayed both author and independent receipts. No correction
was requested.
