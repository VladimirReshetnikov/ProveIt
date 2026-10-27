# Internal negative norms before literal polynomial soundness

27 October 2026. Read-only proposal; no new Lean source, overlay or compiler.
The smallest next pair is `ArithmeticNegativeNorms` and focused Checks.
It removes the actual sign obstruction before signed factor extraction.
All variables below range over an arbitrary internal arithmetic model V.
The common context is ORingStructure V and V models IΣ1. The bounded
induction is not asserted from IOpen alone.

## First pair: exact arithmetic interface

Only these two imports are requested:

```
Foundation.FirstOrder.Arithmetic.IOpen.Basic
Mathlib.Tactic.Ring
```

Proposed public statements (ordinary multiplication notation shown):

```lean
theorem square_mod_four (x : V) : (x*x)%4=0 ∨ (x*x)%4=1

theorem square_discriminant_ne_negative (A x t : V) :
  x*x+t*t+1 ≠ A*A*t*t

theorem consecutive_negative_descent (n x y : V) (hn : 2≤n)
    (h : x*x+1=n*(n+1)*y*y) :
  ∃ u v : V, 0<v ∧ v<y ∧ u≤(n+1)*v ∧
    u*u+1=n*(n+1)*v*v

theorem consecutive_ne_negative (n x y : V) (hn : 2≤n) :
  x*x+1 ≠ n*(n+1)*y*y

theorem main_ne_negative (a x t : V) :
  x*x+1 ≠ ((a+1)*(a+3))*t*t

theorem square_aux_ne_negative (S v y : V) :
  (S*v)*(S*v)+y*y+1 ≠ S*S*y*y
```

The mod4 theorem retains A=0, A=1 and t=0. It makes no Pell-classification
or positivity assumption. The consecutive theorem genuinely requires n≥2:
n=x=y=1 is a negative-norm solution. There is no sign premise on a first
inverse coordinate, and no assumption that a literal tau or rank is positive.
The descent helper may remain private if its proof packaging is simpler;
the complete exclusions and their two displayed corollaries are required.

## Modulo four uses actual internal remainders

`Arithmetic.even_or_odd'` writes x=2*(x/2) or 2*(x/2)+1. Squaring gives
4*k*k or 4*(k*k+k)+1. `mod_mul_add_of_lt`, `mod_add`, `mod_mul`, and the
actual bounded remainder therefore prove `square_mod_four`.
These APIs are all in IOpen.Basic, lines277–396. No ZMod cast, Nat-valued
semantic oracle or enumeration of the entire internal domain is used.

Reduce a hypothetical x²+t²+1=A²t² modulo4. If t² has residue0, the right
side is0 while the left is1 or2. If t² has residue1, the left is2 or3 while
the right is0 or1. The finite possibilities use numeral inequalities in V.
This is the internal version of `ShortEquation.strong_ne_neg_one`.
For the main/strong discriminant, add t² to both sides of a hypothetical
x²+1=(a+1)(a+3)t² and use (a+1)(a+3)+1=(a+2)².
For the auxiliary factor use A=S, x=S*v, t=y directly. Its exclusion does
not require the strong equation to have been recovered first.

## Actual bounded descent for the consecutive factor

Write d=n(n+1), A=2n+1, so A²=4d+1. Suppose x²+1=d*y².
The y=0 case is impossible. Thus y≥1, and n*y²≥2. Comparing squares gives
n*y<x: otherwise x²+1≤n²*y²+1<d*y². Also x<(n+1)*y, hence the needed
non-strict root bound. The exact identity

```
(A*y)^2 = (2*x)^2 + y^2 + 4
```

gives 2*x<A*y. Define v=A*y−2*x only after this strict inequality.
Then v>0, v+2*x=A*y, and n*y<x gives v<y.
The signed inverse root need not be positive. Define

```
u = (A*x−2*d*y) + (2*d*y−A*x).
```

A two-order-case natural identity proves
`absdiff(l,r)^2+2*l*r=l*l+r*r`, using only justified truncated subtraction.
Together with v+2*x=A*y and A²=4d+1, additive ring identities give
u²+1=d*v². One way to cancel without signed arithmetic is to add the common
term 4*A*d*x*y: the two sides reduce to a common polynomial plus x²+1 and
d*y² respectively. The new norm and v>0 give u≤(n+1)*v, completing descent.

Use the bounded invariant

```
P(y) := ∀ x≤(n+1)*y, x*x+1 ≠ n*(n+1)*y*y.
```

It is Δ0 (a bounded universal and quantifier-free matrix), hence Sigma1
definable. `ISigma1.sigma1_order_induction` at Schemata.lean328 applies to
actual internal y. Any hypothetical root lies inside the displayed bound;
the constructed u,v lie inside the induction hypothesis with v<y.
No standard-Nat strong induction, external fundamental-unit theorem or
unbounded arbitrary-predicate induction is substituted. Checks should
include y=0, A=0/1, t=0, the n=1 counterexample, arbitrary internal values,
and axiom audits of every public exclusion.

## Subsequent signed-pair extraction, explicitly outside the first pair

`Expr.splitNatural` is defined in NaturalExpression.lean62–75: subtraction
exchanges the negative components, and multiplication sends pairs (a,b),
(c,d) to (a*c+b*d,a*d+b*c). `ArithmeticExpression.sat_equation` identifies
the compiled equation with equality of these natural evaluations in every
commutative semiring. Its Nat/Int theorem does not provide the missing
all-internal signed-factor theorem.

A later small signed-pair layer can use equivalence a+d=b+c, magnitude
`absdiff(a,b)`, and the identity

```
absdiff(a*c+b*d,a*d+b*c)=absdiff(a,b)*absdiff(c,d).
```

This follows by the four relative-order cases, or by the additive square
identity followed by equality of nonnegative squares. It does not need an
internal Int/Grothendieck quotient. Cancelling positive delta in the actual
scaled expression and taking magnitudes gives a product of five natural
absolute values equal to1. Natural unit extraction makes each magnitude1;
the first four exclusions above choose the positive sign for P,Q,U,strong.
The signed product then forces W=1. It is important to prove these algebraic
pair laws and the actual evaluator binding; a hypothesis saying that the
five desired equations already hold would not close polynomial soundness.

Carrier65.scaled_identity is the exact external guide:
`value=delta*(P*Q*U*W*strong−1)`. Its `value_zero_iff_norms` is over Int and
cannot simply be applied to an arbitrary internal natural model. The later
pair proof must bind the literal `expressionAt`, not merely an equivalent
unrelated ring expression. No new operation/degree metric is proposed.

## Correct order for the maintained scalar client

Before transport, q−F, C, rank and tau may have either signed orientation.
With b=beta*J, q=b+1 and q≥2, represent rank by the pair

```
Rplus  = (b*q+alpha)*(q*q−1)+(MC+q*MF)*J
Rminus = b*F*(q*q−1).
```

Only q*q−1 is truncated here, after q≥2. Represent tau by
`(E*N+k+Rminus,Rplus)`, and V by
`(f*f*c*T+f*f*Rminus,f*f*Rplus+c)`.
Their absolute differences suffice for the squared first/auxiliary factors.
The first discriminant parameter n=E*Y is≥2 from beta,J,w,s positive.
The other polynomial scales a,c,delta,S are nonnegative directly.

W=1 is exactly the additive equation

```
(K+w)*q+q = (K+w)*(F+alpha)+F+z*(q−1)+1.
```

This transport is recovered before invoking `ArithmeticPellFirstIndex.scalar_window`.
That theorem derives C>0, the literal natural rank lower bound and R+2<E
from the port inequalities and positive variables. It therefore identifies
Rplus−Rminus with the actual truncated rank, and forces E*N+k>R. Only now
does the signed first root become the maintained natural tau=E*N+k−R.
V still uses the absolute difference; its sign is never assumed. The
recovered main, strong, auxiliary and first equations are exactly the four
additive norms expected by `maintained_first_indices` and `maintained_power`.
MF is the already shifted source fourth port throughout; no second shift.

Concrete current port certification, syntax-to-pair evaluation and this
transport-first conversion remain later theorem obligations. The first
pair neither imports CurrentEquationSyntax2011 nor claims the displayed
polynomial's all-internal soundness. PowerRecovery's independent acceptance
is also not needed to authorize this smaller arithmetic leaf.

## Minimal cache and provenance

The requested imports have exactly the accepted GcdNormalization prerequisite
DAG:86 custom modules, all86 Foundation,344 custom artifacts,37 explicit
external names and111 total boundary artifacts (37 primaries+74 companions).
There are455 actual first providers, zero refresh. The new read-only auditor
rechecks the complete current headers/DAG, every source/object pin and every
first provider against the accepted ROOT Gcd provider and original package
search. It creates no overlay and launches no Lean.

Selected existing provider: `/tmp/arithmetic-gcd-normalization-root-pnbeaddq/lib`.
The Gcd module itself is not imported. Its accepted ROOT packet is
`b74df44673d2f89c82b6c85237c1e203a03296068dd0f6d455ecf4ad29d14512`;
the unchanged original cache inventory is
`1206727b503151356d3ba49f713e09bf88b84d3d6af131ca6a29625e221c2a14`.
The new inventory pins all inspected mathematical source guides separately
from the86 selected import modules. Existing package/trace provenance
qualifications are inherited; no Foundation/package rebuild is claimed.
Implementation, any broader syntax-union inventory and the two new compiler
commands await ROOT review. Frozen Power and other accepted sources remain
unchanged.

The controller independently challenged the descent arithmetic and zero
cases only, explicitly confirming the bounded Δ0 versus open-induction
distinction. That is not a source implementation or cache/replay review.
