# Ordinary-tail integrality: noncircular proof plan

This is a mathematical plan and an inventory of existing interfaces, not a
Lean proof of the integrality theorem, an iPRA derivation, or compact44
calibration. The finite check below certifies only the stated polynomial
identities and bounded examples. In particular, the graph binding, model
least-number argument, and its object-level proof transport remain open.

## Uniform arithmetic claim and edge cases

Let `q>1`, `v`, `Y`, and `D` be integers, with `D != 0`, and suppose

```
q v² D² = (q-1) Y² + D².                         (1)
```

The desired independently quantified arithmetic lemma is `D | Y`. It makes
no assumption about the 12-variable graph, Pell ranks, a strong norm, or the
compact44 ports. This is the cleared version of the source's rational
integrality lemma. Negating `D`, `Y`, or `v` separately preserves (1), so
normalize their magnitudes; `|D|>0`. Neither `v` nor `Y` can be zero:
with `v=0` the right side is positive, and with `Y=0` cancellation gives
`q v²=1`, impossible for `q>1` and integral `v`.

The strict `q>1` condition cannot be dropped: `q=1`, `v=1`, `Y=1`, `D=2`
satisfies (1), but `D` does not divide `Y`. The free-J ordinary tail also
has `bₙ=0` when `Q=1`, so its subsequent denominator would be undefined.

## Reduction to a fixed denominator

Apply the model gcd certificate to `|Y|` and `|D|`: obtain positive `g,b`,
a natural `a`, and signed Bézout coefficients such that

```
|Y| = g a,  |D| = g b,  ax+by=1,  b>0.
```

Cancel `g²` in (1). The normalized equation is

```
q v² b² = (q-1)a² + b².                         (2)
```

Here and below `v` denotes the positive magnitude. From `(2)`, `b²` divides
`(q-1)a²`. Coprimality of `a²` and `b²` follows constructively from the
explicit identity

```
(ax+by)³ = a²(a x³ + 3b x²y) + b²(3a xy² + b y³).
```

Thus Bézout cancellation gives `b² | (q-1)`; choose a natural `s` with
`q-1=b²s`. No unique factorization, rational arithmetic, or classical
choice of an external standard integer is required. Showing that the
cubic signed-coefficient identity is usable with the model's four-natural
coefficient representation is still a Lean obligation.

An exploratory [universal ring lemma](../square-divisor-witness/README.md)
now supplies an explicit polynomial witness for this divisibility from the
cleared norm and a supplied Bézout certificate. Its bounded compilation
does not yet supply the model-pair representation, natural sign of the
witness, gcd certificates, descent, or the internal iPRA derivation.

## Descent and the induction predicate

From `(2)` we have `v>0` and `a>0`. If `v=1`, cancellation of `q-1>0`
yields `a=b`; the Bézout certificate then gives `b|1`, so `b=1`.

If `v>1`, elementary ordered-ring calculations give

```
a > vb,                 qvb > (q-1)a.            (3)
```

The first follows from `(q-1)(a²-v²b²)=b²(v²-1)>0`. For the second,
`(qvb)²-((q-1)a)² = q b² + (q-1)a² > 0`; both sides are nonnegative.
Define signed integers

```
v' = (2q-1)v - 2bsa,
a' = (2q-1)a - 2qvb.
```

The norm `(2)` holds with `v',a'` in place of `v,a`. Since
`a'-a = b(2bsa-2qv)`, the Bézout certificate for `(a,b)` transforms into
one for `(a',b)`. Taking absolute values retains both properties. The
inequalities `(3)` give `-v < v' < v`; equation `(2)` rules out `v'=0`.
Hence a new witness has the same denominator `b` and a strictly smaller
positive `|v'|`.

A model proof must not simply invoke external well-founded induction on an
arbitrary predicate. Fix model parameters `r=q-1>0` and `b>=2`, and use
least-number induction for the following **Σ₁** predicate, with the signed
Bézout coefficients represented by four naturals:

```
Bad(k) := ∃ a u₁ u₂ u₃ u₄,
  (r+1) k² b² = r a² + b² ∧
  1 + a u₁ + b u₂ = a u₃ + b u₄.
```

All displayed arithmetic is natural; the matrix is quantifier-free in the
ordered-ring language, and the existential tuple can be handled as the
usual finite Σ₁ prefix/coding. An initial reduced counterexample gives
`Bad(v)`. The least `k` with `Bad(k)` is neither zero nor one by the cases
above; the transformed and sign-normalized certificate gives `Bad(|k'|)`
with `|k'|<k`, a contradiction. That `Bad` has the required Σ₁
representability, all magnitude operations, and the descent inequalities
must still be formalized. This argument describes a possible classical
`IΣ₁` model proof; it does **not** itself produce a proof in intuitionistic
PRA, whose separate syntactic transport must be justified.

A potentially more direct iPRA route is to define the complete descent
state by primitive recursion: store `v`, `a`, fixed `b`, the fixed divisor
witness `s`, and natural pairs for the signed Bézout coefficients. If
`v>1`, replace the state by the absolute values of `v',a'` and the updated
certificate; if `v=1`, leave it unchanged. Run at most the initial `v₀`
steps. A candidate quantifier-free invariant, in addition to the cleared
norm and certificates, is `vₖ>0` and `vₖ+k<=v₀+1` for `k<=v₀`; the strict
decrease proves its step before reaching one, and the bound remains true
afterward. At `k=v₀` this gives `vₖ=1`, and the base case gives `b=1`.
Absolute differences, the branch, the fixed-length iteration, and signed
coefficient updates are primitive recursive. This is a proof design, not a
proved iPRA derivation: primitive-recursive gcd normalization with the
needed certificates, well-defined zero/predecessor and sign cases, the
encoded quantifier-free invariant and decreasing measure, and the exact
internal Lean proofs of the iteration all remain to be supplied. In
particular, this alternative does not assume Σ₁ minimization in iPRA.

The more detailed [primitive-recursive design](PRIMITIVE-RECURSIVE-DESIGN.md)
specifies signed-pair coefficient updates, a candidate open induction
invariant, an explicit natural divisor witness, and a possible bounded
Euclidean normalization. These remain proof obligations, not established
object-theory derivations.

## Exact free-J graph instantiation

For the ordinary tail set

```
Q = Δ(f²-1), d = c⁴, w = n+V,
h = (1-Q)w²+QV²-1,
bₙ = 2(1-Q)w, A = d h + Q(1-Q), N = A²-dQbₙ²,
D = d bₙ, Y = wD-A.
```

`FreeJNormZero.cleared_auxiliary_identity` proves over every commutative ring
that `QV²D²-(Q-1)Y²-D²=-(Q-1)N`. Independently, a replayed split for this
free-J graph yields `N=0` at a zero. The generic natural-valued pair
identity in that packet does **not** by itself establish substitution of all
signed graph expressions into the model identity; that remains a graph
transport obligation.

For the graph application one must prove `Q>1`, `d>0`, and `bₙ!=0` from
the actual positive-coordinate hypotheses. Here `Δ=(a+1)(a+3)`, `f=t+1`,
and `c,n,t` are positive, so the first two are expected by elementary
inequalities. For the third, one sufficient route is the manuscript's
early `V>c>1`, which makes `w=n+V>0` without invoking a strong norm. The
replayed early-size packet proves `c>(a+2)Δ²` and `2R<c`, conditional on
its graph/port hypotheses. A later [bounded model replay](../free-j-graph-vbound-prototype/README.md)
proves the signed graph binding and `V>c>1` using those assumptions and
the actual free-J zero. Its theorem explicitly bridges the graph's signed
subtraction to the natural subtraction used in the early-size result; it
does not assume the later strong norm. An [independent bounded replay](../../../reviews/ordinary12-freej-vbound-independent-audit/README.md)
also passed. These historical overlays are not yet an iPRA derivation or a
proof of the specific denominator's nonzeroness. Another proof of `w!=0`
would also suffice for that step, but must be shown from graph hypotheses.

After applying the uniform integrality claim, write `Y=D z` and let
`i₀=w-z`, a **signed** integer. Then `A=D i₀`. From `N=0`,

```
d bₙ² (d i₀²-Q) = 0.
```

Since `d>0` and `bₙ!=0`, cancel to obtain `d i₀²=Q`. As `Q>1`, `i₀!=0`;
choose positive `i=|i₀|` and use `d=c⁴` to obtain
`(i c²)²=Δ(f²-1)`. The integral auxiliary witness is `y=|z|` and satisfies
`Q V²-(Q-1)y²=1`; `u=n-i₀` remains signed, and `y=|V+u|`. Passing to
any theorem that additionally requires positive `u` or a particular sign of
`V+u` needs its own proof. No `Δ|i` is assumed or derived here.

## Existing interfaces versus obligations

* `ArithmeticGcdNormalization.gcd_certificate_exists` returns a common
  divisor and four-natural Bézout certificate in arbitrary `IΣ₁` models;
  `unit_certificate_cancel` derives divisibility cancellation from a unit
  certificate. `norm_normalization` already demonstrates extracting
  normalized factors and a unit certificate by canceling a positive gcd.
  These interfaces do not yet prove the descent above.
* The same source applies `InductionOnHierarchy.least_number 𝚺 1` to a
  directly established Σ₁ predicate. This provides an API example, not a
  ready-made proof that `Bad` is Σ₁.
* `ordinary-descent-step-prototype/FreeJDescentStep.lean` proves conditional
  algebraic norm preservation and Bézout preservation given a divisor
  witness; its README explicitly excludes denominator recovery and descent.
* The [reduced model descent step](../reduced-model-descent-prototype/README.md)
  combines a model square-divisor witness with norm preservation, strict
  bounds and signed certificate transport; its [independent artifact audit](../../../reviews/ordinary12-reduced-model-descent-independent-audit/README.md)
  passed. A later [paired measure replay](../reduced-model-nonzero-prototype/README.md)
  constructs a strictly smaller positive model coordinate and passed an
  [independent artifact audit](../../../reviews/ordinary12-reduced-model-nonzero-independent-audit/README.md).
  The [simultaneous-state theorem](../reduced-model-state-prototype/README.md)
  combines the coordinate, numerator, norm and certificate, and its paired
  replay passed an [independent artifact audit](../../../reviews/ordinary12-reduced-model-state-independent-audit/README.md).
  A [model least-number proof](../reduced-model-induction-prototype/README.md)
  now proves `b=1` from the stated positive reduced norm and certificate;
  its paired replay passed an [independent artifact audit](../../../reviews/ordinary12-reduced-model-induction-independent-audit/README.md).
  A subsequent [natural normalization theorem](../reduced-model-normalization-prototype/README.md)
  constructs the gcd and certificate from the positive natural cleared norm;
  its paired replay passed an [independent artifact audit](../../../reviews/ordinary12-reduced-model-normalization-independent-audit/README.md).
  A [signed difference-ring lift](../reduced-model-signed-prototype/README.md)
  handles arbitrary signs and nonzero denominator; its paired replay passed an
  [independent artifact audit](../../../reviews/ordinary12-reduced-model-signed-independent-audit/README.md).
  The [graph application](../free-j-graph-integrality-prototype/README.md)
  now proves `D ∣ Y` under its stated free-J hypotheses, with an [independent
  artifact audit](../../../reviews/ordinary12-freej-graph-integrality-independent-audit/README.md).
  The subsequent [graph strong-norm theorem](../free-j-graph-strong-prototype/README.md)
  constructs a positive multiplier without assuming the norm; its paired
  replay passed an [independent artifact audit](../../../reviews/ordinary12-freej-graph-strong-independent-audit/README.md).
  A [graph auxiliary-witness theorem](../free-j-graph-auxiliary-prototype/README.md)
  also proves the positive auxiliary norm with explicit sign alternatives;
  its paired replay passed an [independent artifact audit](../../../reviews/ordinary12-freej-graph-auxiliary-independent-audit/README.md).
  The [exact carrier-index theorem](../free-j-exact-ordinary-prototype/README.md)
  subsequently proves `π=R` and `2j=R+1`, with an [independent artifact audit](../../../reviews/ordinary12-freej-exact-ordinary-independent-audit/README.md).
  The distinct `f` exponent `m` is only known to be divisible by `π`.
  Remaining carrier recovery, fixed-port calibration and the object-level
  iPRA proof remain open.
* `FreeJNormZero` proves the generic ring identity and a natural-valued
  signed-pair instance. The general signed graph substitution is open.
* The early-size and index packets give useful intermediate model results
  under explicit assumptions, not the candidate's final iPRA theorem.

Run `python3 check_identities.py` in this directory for five sparse-integer
polynomial identities and an exhaustive **bounded** sanity check, including
the `Q=1` counterexample. These calculations do not certify any of the
unbounded claims or model/graph transports.

The [independent review](../../../reviews/ordinary12-integrality-descent-independent/README.md)
also found that the original checker could print success under optimized
Python with its assertions disabled. The checker now rejects optimized mode.
The normal and optimized process outcomes are recorded in
[`guard-fix-observation.json`](guard-fix-observation.json); a [separate review](../../../reviews/ordinary12-integrality-guard-independent/README.md)
checked the correction under normal and optimized invocation modes.
