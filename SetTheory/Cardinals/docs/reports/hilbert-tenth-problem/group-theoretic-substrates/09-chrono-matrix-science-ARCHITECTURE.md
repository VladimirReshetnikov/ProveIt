# Fixed-arity chronological certificate for the ordinary-input countdown

Research proof and literal source packet, 4 October 2026. This is not an article. It concerns the current 97-choice five-register countdown, equivalently the counted-suffix 195-generator membership predicate. No upstream program or saved accepting schedule is executed.

## 1. Exact current source and theorem

The upstream sources are pinned in `sources/`. Their current-main contents were compared with the requested commits and agree byte for byte:

- `matrix195_counted_suffix.md`, commit `d31e29030214c35083b0c2e052c8a3a5d0409eb0`, Git blob `5b0af4b4c3a6c61f5eee75beed2c1d586b86c519`
- `matrix193_countdown_rows.md`, commit `750aeb4f7834332deb2bec5f32fb470ff8254431`, Git blob `cd83d69f27946448df07b0409e44c81ac0559600`; latest commit affecting this file is still that commit, dated 2026-10-04 04:11:24 UTC
- Countdown receipt at the latter commit, Git blob `d8cdf1509237575bfce3b9c96faf3c883c998412`, SHA256 `f365eb9b62242b395b33766d00a246f0ebcd1a28d867cbcf1173037552b916e0`

The counted-suffix construction has 195 fixed singular integer 7-by-7 generators and target

`T(x)=diag(I_2,P,F+xE_02)`, where `P=[[1,2],[0,1]]`.

Here `x` is the supplied ordinary positive integer itself. Its valid words have the shape `L_(i1)...L_(in) END COUNT^x`, with a nonempty old prefix. This is directed semigroup membership, not an inverse-closed group problem, an SL(7,Z) problem, or mortality.

The equivalent countdown state is `(X0,X1,Y0,Y1,n)`. Its initial state is

`(35426321,-19628667,1,0,x)`.

Its 97 choices are

- LOAD: `X'=X`, `Y'=Y B^-1`, `n'=n-1`, with `B^-1=[[52891,-29036],[94920,-52109]]`
- TILE_i, for the 96 retained tile identifiers: `X'=X K_i`, `Y'=Y G_i`, `n=n'=0`

The endpoint is `X=Y,n=0`. The matrices are the actual `K_i,G_i` in the pinned receipt, not substituted small examples. Row-vector right action is retained. Thus for column storage `z=(X0,X1,Y0,Y1)`, write the fixed maps as `z'=A_i z` with `A_i=diag(K_i^T,G_i^T)`. The loader uses `diag(I_2,(B^-1)^T)`.

The source still reports the local fixture polynomial at 2,065 gates and exact degree 194, endpoint at seven gates, and fixed-duration upper bound `2066h+7` using `5h` signed witnesses. Those are not the ledger of this packet. The upstream ordinary-input countdown has no externally supplied Pell input and no uncharged exact-index condition; its missing part was fixed-arity arbitrary-duration packing.

**Theorem, conditional only on the inherited explicit arithmetic and matrix-interface theorems stated below.** The emitted integer polynomial `P(x,w)` has 41,309 strictly positive integer witness leaves. For every strictly positive integer `x`, it has a positive-integer zero exactly when the pinned countdown has a finite accepting chronological path, equivalently when `T(x)` belongs to the associated 195-generator directed semigroup. All chronology, range, branch, signed-value, input, countdown, and endpoint constraints are included.

This fixture's fixed contexts are `[110` and `A0]`; it is not claimed to initialize every c.e. language. The same fixed-shape construction applies after an arbitrary program's 96 matrix pairs are supplied by the inherited effective initialization/context theorem, with program-dependent fixed numerals and a newly computed radix factor. No arbitrary-program compiler is implemented here.

## 2. Explicit arithmetic dependency

Every POWER and binary-bit containment Sub is fully expanded in `build_certificate.py` and `evidence/polynomial-dag.json`. These are precisely the approved arithmetic equations in the repeated-target packet, with no external representation oracle. The number-theoretic dependency is the constructive Pell theorem at mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, file `Mathlib/NumberTheory/PellMatiyasevic.lean`, theorems `matiyasevic` and `eq_pow_of_pell`, pinned file SHA256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`.

The supplied arithmetic semantics are:

- POWER(b,e) gives exactly `b^e`, for integer `b>=2,e>=0`, using 26 positive witnesses and 15 residuals
- Sub(M,V) gives exactly binary bit containment `V subset M`, for natural M,V, using three POWER calls, five further positive witnesses, and three further residuals

The complete equations and accounting are repeated in `SOURCE_NOTES.md`. No general MRDP representation, unexpanded digit extraction, Hadamard product, variable-length conjunction, sign oracle, or array primitive is used. SPREAD is unnecessary here because the input is the scalar x, and all program coefficients are fixed. This is a specialization of the same approved POWER/Sub vocabulary, not a new unproved arithmetic macro.

## 3. Fixed radix and signed encoding

For branch i and output coordinate r put

`c_(i,r)=1-sum_s A_i[r,s]`.

Choose the following fixed power-of-two numeral once for this alphabet:

`C=2^104=20282409603651670423947251286016`.

It is at least 128 and at least every

`2+sum_s |A_i[r,s]|+|c_(i,r)|`.

The actual maximum including 128 is `18510406623962009412894903228521`; the complete coefficient manifest records it. This is an intentionally conservative fixed bound.

Existentially choose positive integers `ell,h`, use POWER to set `H=2^ell`, and define `D=2H,b=CD`. Positive slacks impose

`H=max_r |initial_r|+initial_gap`,
`x+input_gap=D`.

Thus `H>35426321`, `0<x<D`, and b,D are powers of two with `D<b`. An integer row value z is stored by the unique offset digit `q=z+H`, with `0<=q<D`. Every finite collection of signed values admits this representation after increasing ell. H is a single shared offset, not a sequence of unconstrained signs.

POWER sets `W=b^h`; natural R obeys `(b-1)R+1=W`, hence

`R=sum_(t<h) b^t`.

The horizon h is positive. This loses no path because every accepting path for positive x has exactly x loader steps, hence at least one step. Zero tile steps are still permitted. The theorem deliberately states positive ordinary inputs, rather than claiming an unimplemented zero-duration disjunction at x=0.

## 4. Selector partition and the paid slice lemma

For each of the 97 branches introduce natural E_i and impose

`Sub(R,E_i)`, `sum_i E_i=R`.

The first clauses say each base-b digit of E_i is 0 or 1, with no digits outside `0,...,h-1`. Because the sum of 97 such digits is at most 97 and `b>97`, the sum cannot carry. Therefore exactly one selector digit is 1 at every time position. No missing time, multiple branch, or nonbinary branch is admitted.

For each branch i and row coordinate s introduce natural Q_(i,s) and impose

`Sub((D-1)E_i,Q_(i,s))`.

Since D is a power of two below b, `(D-1)E_i` consists of independent blocks of low binary bits precisely at positions selected by E_i. Consequently Q_(i,s) has an arbitrary digit in `[0,D)` there and digit zero at every unselected position. Define as a source expression

`U_s=sum_i Q_(i,s)`.

The selectors are disjoint, so this addition is carry-free, U_s has digits below D, and Q_(i,s) is exactly the selected whole-digit part of U_s. This proves the **slice lemma** in both directions. Given any bounded U_s, its unique pieces satisfy these clauses. All 388 containment predicates and all sums are emitted and charged; no variable-variable digit multiplication is concealed in the word “selected.”

This specialized partition realizes what could alternatively be built from 388 generic AND calls, but is smaller because the entire branch partition is already certified. Its proof is independent of the transition equations.

## 5. Exact chronology including initial and last frames

Introduce five natural post-streams `V_0,...,V_3,V_n`, each with

`Sub((D-1)R,V)`.

For the counter prehistory N impose the stronger mask

`Sub((D-1)E_LOAD,N)`.

In particular N has digits below D and is zero at every tile position. For each row endpoint f_r use a natural leaf and a positive gap with `f_r+gap_r=D`. Impose

`b V_r+(H+initial_r)=U_r+W f_r`, for r=0,1,2,3,

`b V_n+x=N`.

The initial offset digits are strictly between zero and D, by the H bound. Every stream has h base-b digits in `[0,D)`; each endpoint f_r lies in `[0,D)`. Both sides of each displayed identity are already canonical, carry-free base-b expansions: shifting a stream by b leaves the low position free, and multiplication by W places a final digit above the h pre-digits. Uniqueness of base-b expansion proves

`U_r[t]=q_r(t)`, `V_r[t]=q_r(t+1)`, with `q_r(0)=H+initial_r` and `q_r(h)=f_r`.

Similarly `N[0]=x`, `V_n[t]=N[t+1]` at internal times, and the last post-counter digit is zero. The coefficients above time h are zero. Thus chronology is literal: there is no permutation of rows, cyclic tableau, omitted boundary, or unsupported duration witness.

## 6. Paid affine updates and rigorous carry bounds

For each row r the source imposes one integer equality with nonnegative sides:

`V_r + sum_(i,s:A_i[r,s]<0) (-A_i[r,s])Q_(i,s)`

`    + H sum_(i:c_(i,r)<0) (-c_(i,r))E_i`

`= sum_(i,s:A_i[r,s]>0) A_i[r,s]Q_(i,s)`

`    + H sum_(i:c_(i,r)>0) c_(i,r)E_i`.

All coefficient multiplications, offset products, sums, and comparisons are charged. Although these are packed streams, every time position has exactly one active i. Let

`J_i,r=sum_s |A_i[r,s]|+|c_(i,r)|`.

Before any carrying, either side's coefficient is at most `(1+J_i,r)(D-1)`, because every q digit is at most D-1 and `H<=D-1`. Since `C>=2+J_i,r`, this bound is strictly less than `CD=b`. All coefficients are nonnegative. Therefore both sides really are carry-free, and integer equality forces equality at every time position.

The digitwise equation is exactly

`q_r(t+1)=sum_s A_i[r,s]q_s(t)+c_(i,r)H`.

Subtracting H and using q=z+H gives `z(t+1)=A_i z(t)`. The same i is shared by every row coordinate. This is the actual directed synchronized transition relation, including all negative fixed coefficients. No prior assumption that a candidate history follows the transitions was used in the carry bound.

## 7. Countdown, phase order, and endpoint

Impose `N=V_n+E_LOAD`. The right coefficients are at most D, hence below b. At a LOAD position this says `n'=n-1`; both n and n' are nonnegative and a load has n>=1. At a TILE position the loader-only mask gives n=0 and this recurrence gives n'=0. Thus both original tile guards are enforced, not merely an endpoint counter check.

The chronological counter telescopes from x to zero, so there are exactly x loader positions. Once a tile occurs at zero, a later load would need a positive pre-counter and is impossible. Therefore accepting selector words are exactly `LOAD^x TILE*`.

Conversely, restricting the packed counter to naturals does not discard any accepting path of the upstream signed relation. A signed path ending at zero has exactly x loads by telescoping; its first tile can only occur after x loads, and no later load can occur. All its counter values are consequently in `[0,x]`. The packed representation therefore preserves the entire accepting signed relation, while safely excluding irrelevant local negative-counter edges that cannot reach the endpoint.

Finally impose `f_0=f_2` and `f_1=f_3`. Because the same H is used in all four coordinates, these equations are precisely `X=Y`; terminal n=0 has already been imposed by the counter chronology equation. An empty tile suffix remains valid if its row endpoint succeeds. Under the inherited first-row/lower-marker theorem this corresponds to a nonempty old matrix product containing the central generator, not an empty semigroup product.

## 8. Completeness and exact equivalence

Given any finite accepting path for positive x, let h be its length. The preceding countdown theorem shows h>=x>=1 and every counter is nonnegative. Choose a power-of-two H strictly larger than 35426321 and every absolute row value along the finite path, also with 2H>x. Put D=2H and b=CD. Every row offset and counter fits its specified digit range.

Pack the chronological pre/post digits, endpoints, and the one-hot selector streams. Put each row pre-digit into its selected slice. All masks hold by their elementary binary meaning. Chronology holds by shifting the actual finite histories. The four affine identities hold at every position by the original transitions, so their sums agree. The loader-only counter mask, recurrence, endpoint, and positive gap clauses all hold. Completeness of the explicitly expanded POWER/Sub theorems provides the remaining strictly positive auxiliary witnesses.

Conversely, every positive zero of the emitted polynomial makes every squared residual zero. Apply the well-founded macro semantics, selector/slice lemma, chronology, carry bounds, countdown, and endpoint arguments in that order. They reconstruct an actual accepting finite path of the original 97-choice system on the unchanged x. The pinned synchronized-row and counted-suffix equivalences then give exactly `T(x)` membership. Inherited group membership is obtained inductively from the actual matrices and initial state; it is not a new oracle in this certificate.

## 9. What this proves and does not claim

The literal source closes arbitrary-duration packing for this fixed-program ordinary-input interface using a fixed number of positive witnesses. Its exact degree is 12 and its literal ledger is large, as reported separately. The smaller degree is not obtained by treating the degree-194 local polynomial as a free operation; this packet replaces that local encoding by fully paid branch masks and affine identities.

This is not an improvement on the established 84-operation universal bound, not a claim about a 193-generator Pell391 loader, not a generic three-gate target construction, and not a claim of minimality. It gives no finite-fold/unique-witness or real-witness equivalence. It does not execute or reprove the arbitrary-program initialization compiler, nor newly audit all inherited group/number-theoretic theorems. Exact source accounting and the independently reviewed chronological proof are separate evidence from those explicit inherited dependencies.
