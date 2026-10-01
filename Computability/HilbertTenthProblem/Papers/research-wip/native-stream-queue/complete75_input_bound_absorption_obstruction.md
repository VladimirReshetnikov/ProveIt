# An exact input-translation obstruction to the apparent 87-operation rewrite

Absorbing the term 2d*x into the positive width witness alpha removes
one addition from the complete coupled88 source, apparently giving
**87=47M+40A**. This rewrite is unsound. It introduces an exact arithmetic
symmetry that changes the ordinary input while keeping every factor of
the proposed polynomial unchanged. The symmetry preserves all nineteen
positive supplied witnesses on a translated family obtained from every
original accepting tuple.

In particular the modified compiler for any nonempty finite set accepts
an additional input outside that set. The analogous deletion from
linear-input89 gives an equally unsound **88=47M+41A** source. Neither
rejected count is a universal bound. The result identifies the precise
role of the paid ordinary-input width term, rather than merely observing
that a hypothesis disappears.

## 1. Exact attempted source change

Use the full fixed compiler hypotheses and positive coordinates of
[coupled88](complete75_coupled_index_linear88.md), or of its
[linear input-modulus successor](complete75_linear_input_modulus89.md).
Write ell=2d. Their relevant definitions are

    q=(B−1)J+1,
    C=q−F−Z−alpha−ell*x,
    W=C−Z, u=ell*x+b,
    kappa=u+delta*M, mu=W+a*kappa+rho*H,            (1)

where M=Delta=(a+2)^2−1 in coupled88, and M=a+1 in linear-input89.
The quantities a, H, M and all fixed program numerals are independent
of x, alpha and delta. The ordinary input x occurs in the actual source
only through the single register `scaled_t=ell*x`.

The attempted change supplies a positive alpha_new and computes

    C_new=q−F−Z−alpha_new.                         (2)

In the literal source, delete

    marked_rhs = C_after_alpha − scaled_t

and alias every use of `marked_rhs` to `C_after_alpha`. Keep
`scaled_t=ell*x`, because the input index still needs it. All other
arithmetic instructions and the final eight-factor product remain.
This saves exactly one addition, introduces no witness or equation,
and preserves the nineteen-witness count. The apparent single-polynomial
ledgers are

| Parent | Modified certificate | Modified polynomial |
|---|---|---|
|coupled88|86=47M+39A, one equation|87=47M+40A|
|linear-input89|87=47M+40A, one equation|88=47M+41A|

There is indeed a positive forward map from any parent tuple:

    alpha_new=alpha_old+ell*x.                    (3)

At the same x and delta, equations (1) and (2) then give identical C,
W, kappa, mu and every unit factor. Thus the tempting completeness
argument is valid. The failure is the reverse implication.

## 2. Exact translation symmetry after the deletion

Once the width term is removed, x enters the rest of the program only
through kappa=ell*x+b+delta*M. For any supplied assignment with M>0,
put

    g=gcd(ell,M), L=M/g, n=ell/g.

Apply the change

    x' = x+L,
    delta' = delta−n,                             (4)

and keep alpha_new and all other supplied coordinates fixed. The
computed modulus M does not change. Therefore

    ell*x'+b+delta'*M
      = ell*x+b+ell*M/g+delta*M−ell*M/g
      = kappa.                                   (5)

C_new and W are also unchanged. All eight factors, all their product
registers and the final polynomial agree exactly. Indeed the only
computed registers that can change are `scaled_t`, `odd_index` and
`index_product`; their sum at `index_rhs` is unchanged.

This is an identity on arbitrary integer assignments. No Pell equation,
mask decoding, sign recovery or source equality is used to prove it.
If delta>n and x>0, it also preserves every declared positive coordinate,
and x'>x. More generally any integer j with 0<=j*n<delta gives another
positive assignment at x+j*L with identical output.

## 3. Every original accepting tuple allows a positive translation

It remains to prove that (4) is available on actual parent zeros, not
just on arbitrary off-zero assignments. On any parent positive zero,
the complete ordinary-input theorem gives

    kappa=psi_A(u), A=a+2, u=ell*x+b,

where u is odd. Since d>=4, x>=1 and b>=1,

    u>=ell+1>=9.                                  (6)

For an odd u=2m+1 and Delta=A^2−1, the elementary binomial expansion is

    psi_A(u) = sum_(j=0)^m binom(u,2j+1)
                  *A^(u−2j−1)*Delta^j.            (7)

All terms are nonnegative and the j=0 term is u*A^(2m). Also
A^(2m)=(1+Delta)^m>=1+m*Delta. Hence

    psi_A(u)−u >= u*m*Delta,
    delta_old=(psi_A(u)−u)/Delta
             >=u*(u−1)/2>ell.                    (8)

For coupled88 this delta_old is exactly its supplied input-index
coordinate. Since n=ell/g<=ell, equations (4) and (8) give delta'>0.

For linear-input89 its supplied coordinate is

    delta_linear=(psi_A(u)−u)/(a+1)
                =(a+3)*delta_old>ell.            (9)

The same conclusion follows with M=a+1 and its corresponding gcd.
Thus **every** parent positive zero first extends by (3), then has a
strictly larger input translate (4) with all nineteen witnesses positive
and the modified polynomial still zero. No canonical-subfamily or large
padding assumption is needed for this argument.

The direct inverse of (3) is visibly unavailable on the translated tuple.
At a parent positive zero alpha_old<q, while either M>q. Therefore

    alpha_new−ell*x'
      =alpha_old−n*M<0.                           (10)

The removed subtraction had enforced exactly the positive width margin
which forbids this translation. Equivalently, the translated index u'
can exceed the modulus-sized range used to identify a Pell index from
its residue, even though kappa is unchanged.

## 4. A parametric family of wrong answers for fixed compiled programs

Let S be any nonempty finite set of positive integers. Fix its compiler
numerals once, and let x0=max(S). The complete parent theorem supplies
at least one positive accepting tuple at x0. Apply (3) and then (4).
By Sections 2–3 the modified source vanishes at

    x1=x0+M/gcd(2d,M)>x0

with all supplied witnesses strictly positive. Its fixed compiler
numerals are unchanged, but x1 is not in S. Therefore this modified
source fails the required ordinary-input equivalence.

For S={1}, this already gives a family of explicit symbolic counterexamples:
every original accepting witness tuple determines a second, incorrect
positive input and its complete positive modified tuple by (3)–(4).
The values may be enormous; the proof neither needs nor claims a
numerically materialized full universal Pell witness.

The obstruction applies specifically when the width deletion leaves
all ordinary-input dependence confined to ell*x+b+delta*M with M
independent of x and delta. It is not a lower bound on universal
Diophantine evaluation, and does not exclude a different recoding with
another paid constraint that blocks (4). In particular it does not
invalidate the complete88 polynomial or any of its proved positive
coordinate changes. It rules out this one-gate shortcut in both existing
input-modulus coordinate systems.

## 5. Executable source and checks

The [checker](complete75_input_bound_absorption_obstruction.py) constructs
both rejected schedules from the actual frozen parent DAGs. It audits
the unique deleted gate, operand availability, the remaining x-dependency,
all arithmetic counts and the unchanged positive witness list. Its
[receipt](complete75_input_bound_absorption_obstruction.json) labels both
schedules as rejected rather than candidate universal results.

For each schedule, 512 supplied cases check the whole-polynomial forward
identity (3), the exact translation (4), and equality of every retained
register except the three explicitly moving input registers. There are
384 fully positive cases and 128 cases with signed other fields. Every
positive case checks positivity after translation. The masks are sampled
from the admissible valuation/population family; these off-zero identity
checks do not rely on mask assumptions.

Another 2,484 local odd-input Pell cases check the integral quotient,
bound (8), both moduli and the positive translated quotient, using an
independent recurrence evaluation. These are local input-Pell tests,
not purported full compiler zeros. The counterfamily of Section 4 uses
the already proved existence theorem for complete parent accepting tuples.

Run the checker normally for exact receipt comparison; use
`--write-receipt` only to regenerate the deterministic receipt.
