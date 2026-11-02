# Candidate primitive-recursive descent in iPRA

This is a proof design, not a Lean-checked theorem or an internal iPRA
proof. It refines the proposed route in
`Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/integrality-descent-analysis/README.md`.
The intended object theory is the selected `IPRANativeTheory.nativeTheory`:
intuitionistic first-order logic, symbols for primitive-recursive construction
codes, and induction for quantifier-free formulas with parameters. None of the
primitive-recursive codes, their specifications, or the derivations below has
been supplied here.

## Reduced problem and signed-pair convention

Let `r,b,s,v,a` be naturals satisfying

```
r > 0, b > 0, r = b²s, v > 0,
(1+r)v²b² = r a²+b²,
a x⁺ + b y⁺ = 1 + a x⁻ + b y⁻.
```

Write `q=1+r`. The last equation represents `a*x+b*y=1`, where a signed
quantity `z` is represented by the pair `(z⁺,z⁻)`, meaning `z⁺−z⁻`.
Pairs need not be normalized. Define their primitive-recursive operations by

```
(u⁺,u⁻) + (w⁺,w⁻) = (u⁺+w⁺, u⁻+w⁻),
−(u⁺,u⁻) = (u⁻,u⁺),
(u⁺,u⁻) * (w⁺,w⁻) =
  (u⁺w⁺+u⁻w⁻, u⁺w⁻+u⁻w⁺).
```

Use `p ⊖ q` for truncated natural subtraction and
`absdiff(p,q)=(p ⊖ q)+(q ⊖ p)`. The order comparison and conditionals below
must be implemented as explicit primitive-recursive codes, not treated as
uninterpreted logical case splits.

## One total descent update

For `v>1` put

```
V⁺ = (1+2r)v,       V⁻ = 2bsa,
A⁺ = (1+2r)a,       A⁻ = 2(1+r)vb,
t  = (2bsa, 2(1+r)v),
v' = absdiff(V⁺,V⁻), a' = absdiff(A⁺,A⁻),
y' = y − t*x,
x' = x                  if A⁺ ≥ A⁻,
     (x⁻,x⁺)            if A⁺ < A⁻.
```

The equalities `V=V⁺−V⁻` and `A=A⁺−A⁻` reproduce the descent transform in
the plan. Its ring identity preserves the cleared norm. Also
`A=a+b*t`, so `A*x + b*(y−t*x)=a*x+b*y`; by the indicated sign branch,
`a'*x'=A*x`. Hence the Bézout equality is preserved in signed-pair form.
The branch `A⁺=A⁻` needs no special choice: either sign for zero gives the
same represented product, although the preserved norm later excludes zero
in relevant states.

If `v=1`, stutter without changing the state. Define a total fallback, such as
stuttering, for `v=0`; the invariant below rules out that case on the run.
Fixed parameters `b,r,s` may be passed to the primitive-recursive step instead
of re-encoded in each state. Encode the six changing natural components as a
single natural using a primitive-recursive finite-tuple coding, and define
`σₖ` by primitive recursion on `k`.

## Decrease and quantifier-free induction

For a valid state with `v>1`, the cleared norm and `r>0` yield

```
a > vb,                 qvb > r a.
```

For the second comparison, the difference of the two nonnegative squares is
`(qvb)²−(ra)² = q b² + r a² > 0`. Since `r=b²s>0`, `s>0`; the two
comparisons imply `−v < V < v`. The transformed norm rules out `V=0`:
otherwise it equates zero to `r A²+b²`, with `b>0`. Therefore
`0 < v' < v`. These inequalities, the ordered-natural cancellation they use,
and the pair-encoding of transformed norm preservation must all be proved
inside the selected object theory; Lean's external ring proof alone does not
supply them.

A suitable induction formula, with `v₀,b,r,s` and the initial state among
its free parameters, is the quantifier-free implication

```
k ≤ v₀ →
  [r>0 ∧ b>0 ∧ r=b²s ∧
   (1+r)vₖ²b² = r aₖ²+b² ∧
   aₖxₖ⁺+b yₖ⁺ = 1+aₖxₖ⁻+b yₖ⁻ ∧
   0<vₖ ∧ vₖ+k ≤ v₀+1].
```

Here every `vₖ`, `aₖ`, etc. abbreviates a projection of a fixed primitive-
recursive iteration code, so the displayed formula contains no quantifier.
It is important to use intuitionistic implication, not a classical rewrite
as a disjunction. If `vₖ>1`, discrete strict decrease supplies
`vₖ₊₁+1≤vₖ`. If `vₖ=1`, the state stutters and the bound at `k+1` follows
from the step premise `k+1≤v₀`. Cases are decidable comparisons of naturals;
their decidability and the required arithmetic facts are separate derivation
obligations in iPRA.

At `k=v₀`, positivity and the bound imply `vₖ=1`. The norm gives
`r aₖ²=r b²`; since `r>0`, cancellation and natural-order arithmetic imply
`aₖ=b`. The Bézout equation then gives
`b*(xₖ⁺+yₖ⁺) = 1+b*(xₖ⁻+yₖ⁻)`. One can use the explicit truncated
difference `e=(xₖ⁺+yₖ⁺) ⊖ (xₖ⁻+yₖ⁻)` to obtain `b*e=1` and conclude
`b=1`, rather than introducing an unbounded existential divisor. These
cancellation, difference, and unit facts also require object-theory proofs.

## Obtaining a natural s from the explicit ring witness

The exploratory `SquareDivisorWitness.norm_square_divisor` proves externally,
for a commutative ring and a supplied signed Bézout certificate,

```
q−1 = b² W,
W = (qv²−1)*(a x³+3b x²y) + (q−1)*(3a x y²+b y³).
```

Represent `x,y,W` by the natural pairs above and compute `W⁺,W⁻` by the
polynomial pair operations. Its signed interpretation is the natural equality

```
r + b²W⁻ = b²W⁺.
```

Since `r>0` and `b>0`, order arithmetic implies `W⁺>W⁻`. Thus the explicit
primitive-recursive term `s=W⁺ ⊖ W⁻` satisfies `r=b²s`; no quotient search
or unbounded existential choice is needed for this step. It is still necessary
to prove inside iPRA the pair evaluation of the ring identity, the sign
argument, and the truncated-subtraction/multiplication identities. The
external generic ring lemma is a guide, not a substitute for those derivations.

## Initial normalization remains an obligation

Given the original signed numerator `Y`, nonzero signed denominator `D`,
`q>1`, and the cleared equation, use magnitudes. A candidate fully explicit
PR normalization runs the extended Euclidean update on `(|Y|,|D|)` for at
most `|D|` iterations, stuttering once the second remainder is zero. Each
nonzero remainder decreases below its previous value. Quotient and remainder
are PR via bounded recursion, and the two sets of Bézout coefficients can be
carried as signed pairs. A positive resulting gcd `g` is a common divisor;
PR exact-division terms give `a=|Y|/g` and `b=|D|/g`, and cancellation of
`g` transports the Bézout identity and cleared norm to the reduced state.
A subtlety is that the familiar invariant “every common divisor is
preserved” contains an unrestricted quantifier and is not itself eligible
for open induction. A possible proof avoids it by computing the entire
bounded remainder/quotient trace with primitive-recursive codes. Let `N=|D|`
and define the trace `(Lᵢ,Rᵢ)` with stuttering after the second remainder
is zero; let `g` be the first remainder in the state at step `N`. A second,
bounded backward traversal can carry quotient witnesses expressing both
components of each state as multiples of `g`. For a nonzero `Rᵢ`, use the
explicit identities `Lᵢ₊₁=Rᵢ` and `Lᵢ=Qᵢ Lᵢ₊₁+Rᵢ₊₁`; in a zero-remainder
state use the separately defined stutter case. Equivalently, one may try to
carry `rem(Lᵢ,g)=0` and `rem(Rᵢ,g)=0`, provided all required remainder
identities have already been proved for the explicit PR remainder code. The
base is the final state `(g,0)`. The final backward witnesses give exact
divisibility of the original magnitudes. The forward extended-Euclidean
coefficient state separately supplies the signed Bézout identity for `g`.

This is an **unproved design**, including the backward invariant, its base
and indexing. A trace cannot be treated as a finite external list or a
metatheoretic function on model indices: the selected iPRA proof needs an
actual PR code for the forward state at every index and for the backward
traversal, with state components recovered by PR projections. A simple route
may recompute the forward state at the bounded index `N ⊖ k` at each backward
step rather than encoding a whole variable-length list. If a sequence code is
used instead, its length, element projections, construction, and all needed
bounds and decoding laws must be proved in the same object theory. In either
route, the invariant must be a single quantifier-free formula in those terms,
with `k≤N` expressed as a PR comparison; no hidden “for every trace entry”
quantifier or appeal to external termination is permitted. The second
traversal must also account for the first zero remainder and all subsequent
stuttering states without reading beyond the defined PR trace.

This proposal still needs explicit function codes and quantifier-free
induction proofs of termination within the bound, quotient/remainder
specifications, gcd positivity, exact division, signed Bézout updates and
cancellation. For `D≠0`, `|D|>0`; the case `Y=0` is incompatible with the
cleared equation when `q>1` and must be treated constructively as well.

## Scope

Even a complete proof of this generic descent in iPRA would not by itself
prove the 12-variable consistency equivalence. The actual free-J graph's
polarized ordinary-tail expression must be connected to the cleared identity
and its auxiliary denominator; the graph's port bounds and compact44 checker
calibration must be established; and the graph-level and consistency
statements must be transported through the exact syntax and derivability
interfaces. No current-source build or audit is implied by this draft.
