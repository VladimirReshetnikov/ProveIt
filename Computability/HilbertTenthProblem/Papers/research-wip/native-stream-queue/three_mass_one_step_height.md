# Height specialization for three one-step mass clocks

This is a bounded illustrative source/proof packet, not an improvement to an unbounded-computation substrate. Three actual [target-free-height sources](three_mass_target_free_height.md) accept only after exactly one transition. For those three sources, removing the ordinary clock input `T` from the height saves one addition. The [helper](three_mass_one_step_height.py) and [receipt](three_mass_one_step_height.json) contain every gate of the resulting three complete polynomials. The two-step inc/dec program is explicitly excluded.

The raw relations themselves are simple: all accepted triples have

\[
 y=x+1,\qquad T=192(x+1)+8.
\]

The nop program accepts every natural `x`; zero3 accepts when `3` does not divide `x+1`; positive3 accepts when it does. These statements describe fixed illustrative programs, not a new universal machine, input loader, or numerical universal bound. The native-history circuits below remain unnecessarily large for those simple relations.

## Literal source change and complete costs

The supplied parameters remain natural `x,y,T`, including zero. All 56 witnesses remain strictly positive. The existing input is `n0=5x+1`. Replace the two actual additions

```
bridge_height_without_time = bridge_input + height_slack
h = bridge_height_without_time + T
```

by the single addition `h = bridge_input + height_slack`. The removed intermediate has exactly one consumer; the slack has no other source or comparison use. Every other gate, all 19 comparison pairs, and the full finalizer are copied literally. In particular, the clock quotient witness and its subtraction/multiplication/addition cone remain paid.

| Fixed program | Parent full total | New M + A | New full total | Witnesses | Comparisons | Degree upper bound |
|---|---:|---:|---:|---:|---:|---:|
| zero3 | 467 | 180 + 286 | **466** | 56 | 19 | 1192 |
| nop | 465 | 178 + 286 | **464** | 56 | 19 | 1192 |
| positive3 | 468 | 185 + 282 | **467** | 56 | 19 | 1192 |

Each full finalizer still costs56=19M+37A: 19 differences, 19 squares, and 18 additions. The certificate bodies therefore cost410/408/411. All gates and supplied coordinates are live. Degree1192 is an inherited syntactic **upper bound**, not an exact-degree claim.

## Signed identity and positive embedding

Write `eta` for the child slack. With every other coordinate unchanged, the all-value identity is

\[
 F_{child}(x,y,T,\eta,\mathbf w)
 =F_{parent}(x,y,T,\eta-T,\mathbf w).
\]

Both actual height cones expand to `5x+1+eta`. Exact expression interning after that proved affine cut verifies all 19 comparison operands and the complete output. The identity holds over every commutative ring, but the displayed parent slack can be negative.

Conversely, every parent assignment in its stated domain has an unconditional positive child embedding

\[
 \eta_{child}=\eta_{parent}+T>0.
\]

It preserves the entire height, source and output, even away from zeros. Thus parent completeness immediately gives child completeness. No new huge native witness need be constructed for this direction. There is no claimed bijection of all positive zero tuples, and no unconditional positive child-to-parent map.

A literal nop outer history at `x=0` has `y=1,T=200,n0=1,nf=2,h=2,eta=1`. It satisfies the three outer equations and the complete joined AND interface with positive outer hats/slacks, but the signed parent slack is `-199`. The receipt materializes that outer interface, not the much larger native Pell witness. The inherited positive native-extension theorem supplies the latter existentially.

## Direct soundness without a time bound in the height

Here `h=n0+eta>=2` and `0<n0<h`; no bound on `T` or the target is assumed. The [target-free proof](three_mass_target_free_height.md), [packed-history proof](residue_affine_packed_history.md), and [clock interface](three_mass_unbounded_interface.md) establish native pretyping and chronology without using `T<h` until the final clock argument. We give the needed replacement for that final argument below.

In each actual table, the state modulus is `K=5`, residue modulus `m=30`, and initial/halt/trap controls are respectively `1,2,3`. All slopes are30. For a residue `r` in `1..30`, its source control is `(r-1) mod5 +1`; its destination control is `(d_r-1) mod5 +1`, independent of the quotient. The helper checks all30 rows of each fixed table. Every initial-control row goes either to halt or trap; every other row, including halt and trap, goes to trap. Consequently any nonempty chronological path ending at halt has exactly one step. A longer path cannot return from trap to halt.

For completeness of the bootstrap, unhat the positive words to obtain nonnegative selector words `E_r` and quotient word `W`. These three tables have no exceptional slope-class words. The unchanged global equation is

\[
 J+\widehat W+\beta=P,\quad J=\sum_rE_r,\quad
 B=131072h^2,\quad P=(B-1)J+1.
\]

`J=0` would make `P=1` although `What+beta>=2`; hence `J>=1` and `P>=B`. The equation bounds the word coefficients below `P`, while `(h-1)J<P` since `B>h`. Thus the joined range/selector lanes and prescribed native scale are well typed already at `h=2`. The retained native constraints give dyadic `B,P,h`, `P=B^t`, and `J=1+...+B^(t-1)` with `t>=1`. They select one residue per position and enforce `0<=q_i<h`.

Every current and next state is a positive radix digit, because `m q_i+r_i<=mh<B` and every literal `a_r q_i+d_r<B`. The transport equation

\[
 B N_w+n0=C_w+B^t nf
\]

therefore proves chronological execution by cancelling radix digits from the low end: first `current_0=n0`, then `next_i=current_(i+1)`, and finally `nf=next_(t-1)>0`. No target bound or target positivity is used before this deduction. In particular `y=0` is rejected since `nf=5y-3` would be negative. There is no zero-time history branch: the global bound forced `t>=1`. The actual table argument now forces `t=1`.

The actual clock coefficients in every row are

\[
 c_r=1152,\qquad b_r=200+192\lfloor(r-1)/5\rfloor.
\]

The checker independently expands the literal paid clock expression in all quotient/edge hats, obtaining exactly `1152W+sum_r b_r E_r`. At one step, this is the physical tick `L=1152q+b_r`. It obeys

\[
 0<L\le1152(h-1)+1160=1152h+8<B-1
 \qquad(h\ge2).
\]

For example, the difference `131072h²-1152h-9` is positive at2 and strictly increasing for integers `h>=2`. The unchanged clock comparison is the exact integer equation

\[
 L=(B-1)(\widehat Q_{clock}-1)+T.
\]

Its quotient hat is positive and `T` is natural. If the hat were at least2, the right side would be at least `B-1>L`. Therefore the hat is1 and `T=L`. This proves clock soundness directly, with no upper bound on the supplied `T`. All ticks are positive, so `T=0` is rejected.

Together with the unconditional positive parent embedding, this proves equality of the represented natural raw triples for exactly the three listed fixed programs. The proof does not apply to inc/dec or arbitrary accepting paths of length at least2. The separate [inc/dec obstruction](three_mass_time_free_height_obstruction.md) records the clock alias that blocks such a generalization; that later artifact is a contextual link, not a dependency of this proof.

## Reproduction and finite scope

All fifteen immediate and inherited source/receipt/proof files are byte-pinned. Historical Python is never imported or executed. The probe retains canonical builders, an integer pullback, and a positive parent embedding for reproducibility; it is not being promoted as a new maintained API milestone. No broad hostile-packet or warm-cache API audit is claimed.

The receipt contains the three complete circuits, exact affine-cut/full-output identities, the 57 retained comparison identities, all three literal clock-source expansions, and exact full ledgers/liveness. Supplemental finite tests cover signed and rational evaluations, positive parent embeddings, genuine outer/AND fixtures, small-height tick bounds, and exclusion of inc/dec. Finite checks do not replace the native theorem or prove the general claims by sampling. The receipt records its own source hash and is compared recursively with exact types.

```sh
python /path/three_mass_one_step_height.py --root ROOT \
  --output /path/three_mass_one_step_height.json
python /path/three_mass_one_step_height.py --root ROOT \
  --expect /path/three_mass_one_step_height.json
```

`ROOT` contains the fifteen pinned predecessor files. Without `--root`, it is the helper's directory. All earlier trios remain unchanged.

A separate possible specialization would substitute `clock_quotient_hat=1` after the one-step theorem, eliminating its private clock cone. That change is not implemented or counted here; it would require its own complete-source and projection proof. It offers no improvement to general unbounded-computation encoding either.
