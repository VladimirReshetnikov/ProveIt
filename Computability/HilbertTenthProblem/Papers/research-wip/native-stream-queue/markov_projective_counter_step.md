# Projective Markov coordinates and a paid guarded counter step

This bounded construction removes the common Markov scale from **ratios**, and gives an exact positive-integer one-step graph and finite-history certificate. It does not improve the direct counter evaluator. The homogeneous coordinate must lie inside the scaled matrix block; using the Markov-fixed constant function as denominator would not remove the scale. No universal simulation, fixed-arity unbounded history, or operation minimum is claimed.

## 1. Inherited interface and distinction from earlier projective packets

The frozen `markov_mask_matrix_lift.md` embeds any finite integer matrix family `M_sigma` in a signed cosine block with action `M_sigma/q`. For an affine map `c -> A_sigma c+b_sigma`, its usual homogeneous matrix is

    M_sigma = [[A_sigma,b_sigma],[0,1]].

Starting with `(c,1)`, a word of length t therefore has cosine coefficient vector `q^(-t)(c_t,1)`. Dividing its first coordinates by its last coordinate recovers `c_t` exactly. The last coordinate is a **cosine coefficient in the same invariant block**, not the coefficient of the constant function1: all Markov operators fix that function, and dividing by its coefficient would leave the factor `q^(-t)`.

An affine equality or sign guard can be homogenized when the last coordinate is positive. This does not itself make a quotient of two arbitrary supplied integers integral. Conversely, along an exact affine history, integrality of the initial ratio implies integrality of every later ratio; separate internal quotient witnesses are then unnecessary.

The existing `group_projective_zero_mortality6.md`, Sections1–3 and6, removes a different projective ambiguity using a specific subgroup stabilizer, then pays for fixed physical words. That result does not automatically normalize the present rational Markov scale. The `matrix193_crt_selector.md`, Sections3–4, and `matrix193_positive_crt_duration.md`, Sections1–4, already distinguish a paid local relation from fixed-duration history/input/finalizer charges and from unbounded packing. The present note retains those boundaries and gives a small explicit example, not a replacement for either compiler.

## 2. A concrete two-action system and its masks

Represent a nonnegative integer counter c by the positive hat `C=c+1`. There are two labelled actions:

* ZERO: admitted exactly when `C=1`, with `C'=1`;
* DEC: admitted exactly when `C>=2`, with `C'=C-1`.

Their homogeneous matrices on `(C,1)` are

    M_ZERO = [[1,0],[0,1]],
    M_DEC  = [[1,-1],[0,1]].

The old lift applies with `r=2`, `b=5`, maximum entry L1 norm3, and `q=7`. Writing `c_j(x)=cos(2*pi*j*x)`, the explicit masks are

    a_ZERO = 1+(2/7)(c_4+c_8),
    a_DEC  = 1+(2/7)(c_4-c_3+c_8).

They are respectively at least `3/7` and `1/7`, and their nonconstant frequencies are not divisible by5. Their common cosine block on frequencies1,2 is exactly `M/7`, by the inherited finite Fourier identity. The guards do not follow from positivity of either mask: an unrestricted matrix word could apply ZERO at a nonzero counter or DEC at zero. The next sections charge their selector and guard equations explicitly.

## 3. Fully paid one-step graphs

All supplied ports in this section are strictly positive integers. Let `B` be a positive selector hat and put `e=B-1`. The direct graph at supplied endpoints `C,C'` is the zero set of the sum of squares of

    r_b = (B-1)(B-2),
    r_z = (B-2)(C-1),
    r_t = C'-C+B-1.                                  (1)

The first equation forces `B=1` or2. If `B=1`, the second forces `C=1` and the third gives `C'=1`. If `B=2`, the third gives `C'=C-1`; positivity of `C'` forces `C>=2`. Conversely every legal step satisfies (1). No range oracle or uncharged Boolean choice is used.

A literal schedule computes `e=B-1`, `t=B-2`, `u=C-1`, then `r_b=e*t`, `r_z=t*u`, and `r_t=(C'-C)+e`. These residual producers cost `2M+5A`. Squaring and joining the three residuals adds `3M+2A`, giving

    direct one-step graph: 12 = 5M+7A,
    one positive auxiliary B, exact degree4.

For an actual raw Markov step, additionally supply positive integers `X,H,X',H'` and require

    X=H*C,       X'=H'*C',
    7X'=X-eH,    7H'=H.                               (2)

Retain `r_b,r_z` and replace `r_t` by the four residuals of (2). These six equations imply (1): substituting the links and `7H'=H>0` into the first Markov equation gives `C'=C-e`. Conversely any legal direct step extends by taking an arbitrary positive `H'`, and setting `H=7H'`, `X=HC`, `X'=H'C'`. The graph projection onto `C,C',B` is exact. Its scale fiber is not claimed unique.

The two Boolean/zero residuals, two links, and two raw Markov equations cost `7M+8A` before their finalizer: two guard multiplications; two link multiplications; `eH`; two multiplications by7; and all eight additions/subtractions. Six squares and five joins yield

    raw homogeneous one-step graph: 26 = 13M+13A,
    five positive auxiliaries B,X,H,X',H', exact degree4.

Thus this specified raw graph costs14 operations and four positive auxiliaries more than the direct graph. The auxiliary count treats the same `C,C'` as supplied endpoints in both cases. It is an upper-bound comparison, not optimality of either graph.

The integrality links in (2) are meaningful. Omitting them and allowing arbitrary positive `X,H` admits `B=2`, `(X,H)=(21,14)`, `(X',H')=(1,2)`: the raw Markov equations and homogeneous zero guard hold, but the ratios are `3/2 -> 1/2`, not integer counter hats. Conversely canonical normalization `H=1` would require `H'=1/7`, which has no positive-integer solution. Rescaling the rational image by7 restores the integer representative `(C-e,1)` and gives precisely the direct affine step; that rescaling is not a new integer operation saving.

## 4. Fixed-duration histories, input and endpoint

Fix an integer `T>=1`. The ordinary input is a positive integer x. Start with counter `c_0=x` and require `c_T=0`. This particular system has a unique legal counter path: decrement while positive, then remain zero. Hence acceptance is exactly `x<=T`; it is not a universal language.

### Direct certificate

Compute `C_0=x+1` with one addition. Supply positive `C_1,...,C_T` and `B_0,...,B_(T-1)`. For every step use the three residuals (1), sharing the adjacent endpoint, and add `C_T-1`. Square all `3T+1` residuals and join them. The complete literal ledger is

    M = 5T+1, A = 8T+2, total = 13T+3,
    positive witnesses = 2T, exact degree4.             (3)

This includes the input addition, all selectors and guards, endpoint subtraction, squares, and joins. The Boolean square has a nonzero fourth-degree leading term, so the upper bound4 is exact.

### Homogeneous certificate with inductive integrality

Supply positive `H_0`, all `X_j,H_j` for `1<=j<=T`, and all selectors `B_j`. Compute `C_0=x+1`, then `X_0=H_0*C_0`, costing `1M+1A`. There are no supplied intermediate counter quotients. At every step use

    (B_j-1)(B_j-2)=0,
    (B_j-2)(X_j-H_j)=0,
    7X_(j+1)-X_j+(B_j-1)H_j=0,
    7H_(j+1)-H_j=0,                                  (4)

and end with `X_T-H_T=0`.

Because every `H_j` is positive, dividing the last two equations *in the proof* gives

    X_(j+1)/H_(j+1) = X_j/H_j - (B_j-1).

The initial quotient is the integer `x+1`, so all subsequent quotients are integers inductively. Their positivity and the other two equations give exactly the same ZERO/DEC guard proof as Section3. The endpoint ratio is1. Thus (4) is sound without unpaid quotient variables or an assumption that arbitrary projective integer coordinates have integral ratios.

For completeness choose any positive `H_T` and define `H_j=7^(T-j) H_T`, `X_j=H_j C_j` along the direct path. These formulas prove existence; the source neither evaluates a variable exponent nor treats division as a primitive. They also show the raw coefficient scale cannot stay normalized: every integer solution has `H_0=7^T H_T`. Requiring `H_0=1` would destroy every positive-integer history of positive duration. The certificate represents a freely scaled input ray, not the single unscaled input function.

The four step residuals cost `5M+6A` per step. With the paid initialization and endpoint, followed by `4T+1` squares and `4T` joins, the complete ledger is

    M = 9T+2, A = 10T+2, total = 19T+4,
    positive witnesses = 3T+1, exact degree6.            (5)

The degree increase is genuine under the ordinary input binding: the first zero guard is `(B_0-2)H_0*x`, whose square has the monomial `B_0^2 H_0^2 x^2`. Other highest squares cannot cancel it over the reals. All residuals have degree at most3. The homogeneous history therefore costs `6T+1` more operations and `T+1` more positive witnesses than (3), with higher degree. This comparison already removes all intermediate quotient links that are redundant by induction.

Nothing asserts (3) is optimal even for the projected language `x<=T`; that elementary inequality has much shorter certificates if the actual selected history is not required. Nor does quantifying the duration turn either family into a polynomial of fixed arity.

## 5. Fresh evidence and scope

The new standard-library checker saves the complete direct/raw local arrays and both complete history arrays at `T=1,2,4`: eight arrays,283 paid rows. It independently checks graph closure, unique destinations, liveness of all supplied ports, operation ledgers, and degree upper bounds. It tests432 small lifted local tuples and13 constructed histories, including rejecting `x>T`, and records the omitted-integrality counterexample. These are corroboration; the all-size soundness, integrality induction, completeness, exact degrees and formulas (3)–(5) are proved above.

Only the new graph generator/evaluator was run. No supplied, frozen or predecessor program, source array, helper or builder was executed or imported. Prior notes were read as inert text. No repository or Git state was changed. The source family/mask compilation is fixed finite rational data, not a free analytic primitive, and there is no external universality theorem in this argument.

The result provides a useful interface but no cost improvement: homogeneous ratios eliminate the *mathematical target scale*, while a paid integer source must either retain a finite denominator-clearing scale or return to the direct affine numerator updates. It leaves open whether some different guarded matrix system has useful shared arithmetic; it proves no general lower bound against all projective encodings.

## 6. Authenticated dependencies and replay record

The exact inert reading spans and hashes are also in the receipt.

| Prior note | SHA-256 | Inclusive read lines |
|---|---|---|
| `group_projective_zero_mortality6.md` | `c0f3cb53d8a189dd7b98e0deb892a75e64426e8ac480ee049f945ed09e896bc2` | 1–125, 185–280 |
| `markov_mask_matrix_lift.md` | `5dca0ea91dc1d05b7e1a784e2933a67c059e99f3db0dad74f8491849345e69e6` | 1–104 |
| `matrix193_crt_selector.md` | `3e8e8323f98712db79d791c80e0f8acf1f859231fbf80f02742fab6dd44d733c` | 115–190 |
| `matrix193_positive_crt_duration.md` | `f2d9113f9c6aae1cffe2e84a38d9e9e63740bb0d5bb6359dd66bdb8ac81bc27c` | 1–100 |

New evidence files:

* `markov_projective_counter_step_checks.py`: `afa674624e4991e014f56593ada2ed093be22be7717e8565ca0b58b40726caeb`.
* `markov_projective_counter_step_checks.json`: `ec34cd98a4330ba04c90c7304bc446950bb85ddbc206771684f1159aec678396`.

The new writer and fresh normal/optimized exact receipt checks from `/` passed before freeze. These checks do not certify any earlier program or source.

The checker takes `--root` pointing to the directory containing the four pinned prior Markdown files; `--expect` checks this saved receipt without writing it.
