# Primitive-recursive radical-tower arithmetic: audit

This note audits the finite algorithms and their majorants. It is a
mathematical implementation audit, not a Lean compilation report.

## Data and invariant

A valid tower of height n is a sequence

    F_0 = Q,  F_j = F_(j-1)(s_j),  s_j >= 0,  s_j^2 = r_j,

where r_j is represented over the preceding stage and is nonnegative.
An element at level j is represented by a pair `(a,b)` for `a+b*s_j`.
The pair representation is allowed to be redundant. In particular,
coefficientwise equality is NOT the field equality test.

At the bottom, use an unreduced signed integer numerator p and positive
integer denominator q. Reduction by gcd is unnecessary. Every initial
numerator and denominator, including all coefficients of every radicand,
has absolute-value bit length at most H, where H >= 1. Negative signs are
stored separately. Zero, one and minus one require at most this budget.

The flattened representation at height j has 2^j rational coefficient
slots. A tower has sum_(j=1)^n 2^(j-1) = 2^n-1 radicand slots. Flattening
does not presume independence of the squarefree monomials.

## No same-height recursive cycle is needed

Use the basic operation set `neg`, `add`, `mul`, `sign`, `inv`.
Each operation at positive level j makes a bounded number of calls only
to level j-1 operations. Comparisons and division are wrappers.

### Negation and addition

    -(a+b*s) = (-a)+(-b)*s
    (a+b*s)+(c+d*s) = (a+c)+(b+d)*s.

Each uses two lower-level calls.

### Multiplication

    (a+b*s)(c+d*s) = (ac+bd*r)+(ad+bc)*s.

This uses five lower-level multiplications and two additions, for seven
lower-level calls in total.

### Sign

First compute sign(r). If r=0, return sign(a). If r>0, compute signs of
a and b. Zero coefficients and equal nonzero signs settle the answer.
If a and b have opposite signs, compute

    D = a*a - b*b*r.

For a>0>b, return sign(D); for a<0<b, return -sign(D).
These rules follow from monotonicity of squaring on nonnegative elements.
The worst branch uses four lower-level sign calls, three multiplications,
one addition and one negation: nine lower-level calls.

### Inversion, including a redundant extension

Compute

    N = a*a - b*b*r.

If N is nonzero, return `(a/N, -b/N)` using ONE lower-level inverse of N.
If N=0, use signs of a and b:

* If a=0, then b*b*r=0, so a+b*s=0. Return the totalized default zero.
* If a and b have opposite nonzero signs, a+b*s=0. Return zero.
* If a and b have the same nonzero sign, a=b*s, hence a+b*s=2a.
  Return the scalar inverse of `a+a`, with second coefficient zero.

The remaining possibility b=0 but a nonzero contradicts N=0 and cannot
occur in a valid tower. Its implementation may also return the default.

This avoids calling sign on the original same-height element. The largest
branch uses at most thirteen lower-level calls: five multiplications,
at most two negations, at most one addition, at most three sign calls,
and one inverse (this sum is twelve; thirteen is a slack upper bound).
In particular, sixteen lower-level calls uniformly bound every basic
operation. Division calls one inverse and one multiplication; comparison
calls negation, addition and sign.

The norm-zero branch is essential. Using the conjugate formula alone
would fail when a new square root already belongs to the preceding field.

## Call-tree bound

For one basic operation at height n, the full recursive call tree has
branching at most 16 and depth at most n. Thus it has fewer than

    16^(n+1)

nodes. This bounds bottom rational operations as well. Constant-factor
stack administration, comparison/division wrappers, reading the rational
slots, and validating all n radicands can be absorbed into

    M(n) = 2^(16*(n+1)).

For example, a generous bound for these combined tasks is

    100*(n+5)*16^(n+1),

which is less than M(n) for every n>=0. Constants can be made literal
instruction counts once a particular stack evaluator is chosen.

M(n) counts rational operations and bounded evaluation administration;
it is not a claim of M(n) elementary bit operations. Rational arithmetic
itself is implemented by the usual fixed primitive-recursive integer
operations. No interpreter for arbitrary primitive-recursive programs is
involved.

## Coefficient-size bound

If all current rational numerators and denominators have bit length at
most B, an unreduced rational addition has numerator bit length at most
2B+1 and denominator bit length at most 2B. Multiplication gives at most
2B; negation, sign and rational inversion do not increase the bound.
Consequently a uniform bound after one bottom rational operation is

    B_next <= 2B+1.

After L such operations,

    B_L+1 <= (H+1)*2^L.

It is therefore safe to use

    B(n,H) = (H+2)*2^(M(n)).

This is precisely `(H+2)*2^(2^(16*(n+1)))`. It is deliberately loose,
but completely primitive recursive. Copying a radicand does not increase
the coefficient budget, since all radicands were included in H.

For any fixed finite sequence of K field operations, replace M(n) by
K*M(n), or iterate the one-operation bound K times. If K is itself a
primitive-recursive bound on an enclosing geometric algorithm, the
resulting bound remains primitive recursive.

## A completely finite implementation

A recursive description can be compiled to a stack evaluator with
level-tagged frames. Every child frame has a smaller level; after at
most M(n) frame-operation units the requested arithmetic evaluation is
finished. Use a bounded loop with this budget and return zero if it
expires. The call-tree estimate proves expiration cannot occur for a
valid input. Invalid syntax is rejected by a separately input-bounded
parser and receives fixed default outputs.

For a numerical register-code majorant, choose

    D = 2^(B(n,H)+2),
    S = M(n)*2^(n+4).

Encode signed numerators and positive denominators as base-D digits;
S digits suffice, very generously, for all rational coefficients in all
retained frames, inputs, and tower data. The complete numerical register
code is then less than

    D^S = 2^((B(n,H)+2)*S).

Indices, masks, digits, bounded folds, stack updates, the loop budget,
and this register bound are fixed primitive-recursive functions. One
need not use a nested pairing whose size is awkward to track. A length-
prefixed binary encoding is interchangeable with this bounded base-D
encoding through primitive-recursive functions.

## Quantifier-free induction discipline

There are two distinct obligations.

1. **Algorithm totality and bounds.** Fix tower code, height n, input
   coefficient budget H, and requested operation as parameters. A state
   invariant records well-formed frames, decreasing child levels, the
   available step budget, and the current coefficient bound
   `(H+1)*2^t-1`. All ranges are bounded and all tests are PR Boolean
   folds. Thus the induction formula is an equation `Inv(t,state)=1`.

2. **The ordered-field laws of the representation.** Do not induct on
   the unbounded formula 'for every field element, all laws hold at
   height j'. Fix a total height N and a budget H. Choose a fixed finite
   family of elementary algebraic and order-law proof templates. The
   article's "One ordered quadratic stage" lemma supplies this family:
   congruence and sign invariance, commutative-ring identities, sign
   trichotomy and negation, closure of positivity under addition and
   multiplication, and the nonzero-inverse identity. Its proof handles
   redundant stages using explicit local root witnesses; addition uses
   base-field lower/upper cuts and multiplication uses the four norm-sign
   cases. Let K
   bound the number of lower-stage operations needed by any template,
   and put

       F_N(B) = (B+2)*2^(K*M(N)),
       H_j = F_N iterated (N-j) times at H.

   The invariant at height j is the Boolean conjunction of these laws
   for all coded argument arrays whose coefficients have bit length
   at most H_j, using the fixed valid prefix tower. This is a finite
   bounded conjunction, hence a PR Boolean value. Every lower-stage
   argument generated by a height-(j+1) proof template falls inside H_j.
   A bounded tuple-enumeration induction establishes the next Boolean
   conjunction. Both inductions use equations, not quantified induction
   formulas. At j=N, extract the desired instances. The universal
   closure over the original parameters is taken only afterwards.

K is a fixed constant determined by the chosen finite local proofs;
it is not a universal program evaluator or a search for an unknown proof.
The particular numerical K belongs in the eventual formal build audit.
The algorithmic M(n) and B(n,H) bounds above do not depend on this
formal-proof-template choice.

Equivalence of different pair codes is encoded by `sign(x-y)=0`.
The internal geometry uses this PR equality predicate, not equality of
the raw natural-number codes. Proving compatibility of operations and
the ordered-field axioms for this predicate is part of the field-law
stage; it must not be omitted by treating redundant pairs as a literal
two-dimensional field basis.

Accepting an external Python trace does not supply a general reflection
principle in iPRA. The final Lean construction must provide the actual
`Prf PRAAx` derivations of these invariant lemmas and their uses.
