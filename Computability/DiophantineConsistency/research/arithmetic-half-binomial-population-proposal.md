# Internal half-binomial extraction and the population lower bound

27 October 2026. Read-only mathematical proposal by controller_certificate.
No Lean source, cache overlay, compiler invocation or dependency refresh was
created. This is a route to new internal theorems, not a claim that the
population endpoint is already proved in IΣ1 or HA.

## Existing source bindings and their limits

The external NativeHalfBinomial.source_half_binomial obtains
`R=2r+1` and `2Y=choose(2r,r)+wX`. Its estimate passes through real quotients,
but the relevant proof is finite: Pell recurrence growth, a perturbation
inequality, a finite binomial expansion and integer rounding. The external
NativePopulationLower.source_population_lower then uses central-binomial
2-adic valuation to prove `3h+2 <= population(R)` when `q=2^h`.
These theorems quantify over ordinary Nat, use Nat.choose/Finset and Mathlib
real arithmetic or padicValNat, and cannot themselves be imported as internal
arithmetic-model correctness.

Accepted ArithmeticPellFirstIndex.maintained_first_indices supplies actual
internal `n>=5`, `2n=R+1`, `k=2*ycoord n B`, `c=ycoord R a`, where
`a=Y*(X+1)` and `B=2*(X*Y*Y-1)+1`. Its scalar_window supplies the genuine
positive transport gap. Put `r=n-1`; then `r>=4`, `R=2r+1` and `n=r+1`.
The external source's stronger `r>=12` is unnecessary for this route.

Accepted ArithmeticPellPowerRecovery.maintained_power gives
`X=Exp.exp R` and `Exp.exp R<Y` from the same actual equations. Its public
y_lower/y_upper give uniform internal one-step Pell growth. Accepted
ArithmeticCarrierRadix2011.current_radix binds these facts to the actual
maintained splitNatural zero and derives an internal positive block count L,
`q=Exp.exp(width*L)`, and the remaining factor exponent. The fixed width is
94517 and the fourth port is highPort+beta once. L is not coordinate v9;
r is the half-index, a third distinct quantity.

ArithmeticBinaryPopulation is a ROOT-authored draft at the time of this audit,
not yet a selected accepted provider. Its fixed Sigma1/Delta1 graphs, totality,
population_even, population_odd, population_div_mod and population_le are
exactly the useful interfaces. Nothing below silently treats that draft as
accepted. No current arbitrary-internal binomial, factorial or general prime
valuation API was found in the inspected Foundation arithmetic tree or current
arithmetic leaves. Searches for ordinary `choose` instances mostly hit
Classical.choose, not a represented binomial coefficient.

## The smallest useful complete comparison theorem

Introduce a represented variable-base power `Pow(x,t)` by PR.Blueprint with
zero value 1 and successor value x*previous. Its fixed Sigma1 result graph,
Delta1 graph and totality follow from the already used PR.Construction APIs.
All x,t are internal. Lean's `x ^ n` with n:Nat is not a replacement.
Needed laws are zero/successor, positivity, product/addition of exponents,
monotonicity in a positive base and exponent, and `Pow(2,t)=Exp.exp t`.
Each has a Delta1/positive Sigma1 invariant with base parameters fixed before
induction. This is infrastructure, not the half-binomial theorem.

A particularly useful first complete arithmetic inequality is:

```
2*r*e <= a -> a*Pow(a+e,r) <= (a+2*r*e)*Pow(a,r).
```

It holds also at r=0, a=0 and e=0. Induct on r with the displayed bound as
an implication. For the successor use the smaller-index bound and
`(a+2*r*e)*(a+e) <= a*(a+2*(r+1)*e)`, whose surplus is exactly the
nonnegative `e*(a-2*r*e)`. Thus the real reciprocal/Bernoulli machinery in
Ratio90.one_add_pow_le is unnecessary. No order-complete field is required.
The implication has a bounded arithmetic antecedent and Delta1 terms; this
is a genuine IΣ1 induction, not induction on an arbitrary Lean predicate.

The recommended first substantive Pell endpoint is the following full
integer sandwich. Let `X,Y,r,k,c,eta,zeta` be internal, with X,Y>=1, r>=1,
`72*r<X+1`, `16<=Y*(X+1)`, and only the actual coordinate/interval hypotheses

```
a = Y*(X+1),       B = 2*(X*Y*Y-1)+1,
c = ycoord(2*r+1,a),
k = 2*ycoord(r+1,B),
c = k*Y+eta,       k = eta+zeta,       eta>0, zeta>0.
```

For `N=Pow(X+1,2*r)` and `D=Pow(X,r)`, conclude

```
k*N < 2*c*D       and       2*c*D < k*(N+D).
```

These coordinate hypotheses are transparent inputs of a reusable lemma,
not disguised ratio hypotheses. The subsequent actual-zero client must
discharge them with FirstIndex/PowerRecovery. In particular it must retain
the factor two in k. No real ratio estimate is an input to this theorem.

Here is the denominator-cleared proof, including the difficult upper error.
Use ordinary base notation `A=a+2`, `P=2*X*Y*Y+1=B+2`, and set
`Q=2*P-1=4*X*Y*Y+1`, `W=(X+1)^2`, `Z=(2*A)^2*X`.
The equality B+2=P is justified from X*Y*Y>=1 before any subtraction rewrite.
All displayed squares have fixed numeral exponents.

1. Existing y_lower/y_upper, internal induction and Pow laws give
   `Pow(2*A-1,2r)<=c<=Pow(2*A,2r)` and
   `Pow(Q,r)<=k/2<=Pow(2*P,r)`. In the implementation use the actual
   positive K=ycoord(r+1,B), k=2K, avoiding division here.
2. The finite polynomial inequality
   `2*P*(X+1)^2 < (2*A-1)^2*X` gives `k*N<2*c*D`.
   The strict c<k*(Y+1) then gives `N<2*(Y+1)*D`.
3. The finite polynomial upper_key from Ratio90 is
   `Z*a <= Q*W*(a+9)`, under the stated a>=16 bound.
   Raise to the internal r. Apply the new integer perturbation bound with
   e=9 (18r<=a follows from 72r<X+1 and Y>=1). Cancel the positive Pow(a,r)
   to obtain `a*Pow(Z,r) <= Pow(Q*W,r)*(a+18*r)`.
4. Since `c*D<=Pow(Z,r)` and `Pow(Q*W,r)<=K*N`, get
   `2*a*c*D <= k*N*(a+18*r)`.
5. The already proved lower comparison and source interval give
   `18*r*N < 36*r*(Y+1)*D <= 72*r*Y*D < a*D`.
   Thus `k*N*(a+18*r) < a*k*(N+D)`. Cancel a>0 to obtain the upper sandwich.

This proof has no circular use of the sharp upper estimate. The crude bound
on N used in step 5 comes only from the lower estimate and source interval.
The main finite coefficient inequalities still need fresh internal ring/order
proofs; existing Nat lemmas are source guides, not internal premises.
For the actual source, `X=Exp(2r+1)` and r>=4 discharge 72r<X+1 by a small
Sigma1 successor induction (base r=4, exponential step multiplies by 4).
X>=16 and Y>=1 give the remaining size bound.

A sensible division of implementation is a small InternalPower pair followed
by a complete PellHalfRatio pair. Combining them is possible but should not
hide that only the latter discharges the actual comparison obligation.
No binomial or population statement follows from InternalPower alone.

## Binomial extraction with integer remainders

A new represented binomial is genuinely needed; do not put a supplied central
coefficient or digit identity in the public population theorem. One concrete
construction is an internal HFS/Seq Pascal row. Start with [1]; form each next
row by a represented bounded traversal, adding adjacent total lookups with
zero outside the old row. Use PR.Construction for both traversals, fixed
formulas and the actual length/lookup guards. Define `Choose(n,k)` as the kth
entry for k<=n and zero otherwise. Prove Pascal, edge entries, symmetry,
positivity in-range, row sum `Exp.exp n`, and the expansion of Pow(X+1,n).
All universals over columns are bounded by the represented row/index; there
is no external List or Fin n with n:V. The two nested inductions can be IΣ1
with fixed graph definitions and bounded universal Sigma1 invariants.

For r>=1 and Exp(2r)<X, this yields actual Q,v,w with

```
Pow(X+1,2r) = Q*Pow(X,r)+v,
v < Pow(X,r),
Q = Choose(2r,r)+w*X.
```

Take v to be the sum of terms below degree r. Its internal sum bound is
`v*X <= Exp(2r)*Pow(X,r) < X*Pow(X,r)`; cancel X>0.
The higher terms are divisible by X^(r+1). No exact real fractional part,
analytic tail estimate or stronger quarter-tail bound is needed.
For r>0, `Choose(2r,r)=2*Choose(2r-1,r-1)` follows from symmetry and Pascal
(or the factorial identity below); this supplies evenness. X=Exp(2r+1)
is also even, hence Q=2t for an actual internal t.

Now combine the integer sandwich with c=kY+eta, 0<eta<k:

- `k*(Q*D+v)<2*c*D<2*k*(Y+1)*D` gives `t<Y+1`.
- `2*k*Y*D<2*c*D<k*((Q+1)*D+v)<k*((Q+2)*D)` gives `Y<t+1`.

Discrete order forces t=Y. Thus the complete derived identity is
`2*Y=Choose(2r,r)+w*X`. This tiny rounding lemma is reusable infrastructure,
but only its composition with the proved Pell sandwich and actual expansion
is the internal half-binomial endpoint. Supplying either desired identity as
a hypothesis would not close the source problem.

## Population without general Kummer or a valuation function

Define factorial F(n) and odd product G(n) by fixed PR graphs:
`F(0)=G(0)=1`, `F(n+1)=(n+1)*F(n)`, `G(n+1)=(2n+1)*G(n)`.
Prove positivity, oddness of G and the exact split
`F(2n)=Exp(n)*F(n)*G(n)` by Sigma1 successor induction. No arbitrary
permutation of an internal finite product is needed for this split.
The Pascal construction must also prove the actual factorial identity
`F(n)=Choose(n,k)*F(k)*F(n-k)` for k<=n; bounded-column induction on Pascal
is a finite algebraic proof. This identity is an outstanding hard fact, not
an available internal theorem or a caller premise of the final endpoint.

Using the population graph once accepted, prove by induction on a binary
length bound t:

```
forall n<Exp(t), exists H,z,
  H=2*z+1 and F(n)*Exp(population(n))=Exp(n)*H.
```

This is a bounded universal Sigma1 invariant. For n=2m or 2m+1, m<Exp(t)
at the successor bound; apply the factorial split, the induction hypothesis,
and population_even/odd. The new odd factor is H(m)*G(m), optionally
multiplied by 2m+1. The zero case has H=1. Specialize at a length exceeding n.
No unbounded universal or arbitrary-predicate induction is invoked.

At r and 2r, combine this identity with the central factorial identity and
population(2r)=population(r), then cancel positive Exp(2r), to obtain

```
Choose(2r,r)*H(r)^2 = Exp(population(r))*H(2r),
```

where H(2r) is odd. Consequently

```
Exp(m) divides Choose(2r,r) -> m <= population(r).
```

If m>population(r), write m=population(r)+1+d. Cancel the common positive
power of two in the displayed identity. It says the odd H(2r) is even,
a contradiction modulo 2. This proves exactly the implication needed by
source_population_lower. General p-adic valuations, full Kummer, or even
the converse divisibility characterization are not prerequisites. The r=0
case is legitimate; divisibility of 1 forces m=0. Central evenness for r>0
can remain the separate Pascal identity above.

## Actual maintained endpoint and remaining boundaries

After the above facts and BinaryPopulation are accepted, the actual client
must take only positivity plus the current fourteen-variable split zero.
Invoke current_equations, maintained_first_indices and current_radix at the
same vector. Write h=width*L, q=Exp(h), X=Exp(R), Y=s*q^3.
The scalar rank formula has coefficient at least 1, so R>=q^2-1; q>=16 gives
R>3q. Since h<Exp(h)=q, derive 3h<R, hence 3h+1<=R.
Therefore Exp(3h+1) divides both 2Y and wX in the half-binomial identity.
Modulo that positive power, the identity gives divisibility of Choose(2r,r).
The new factorial/population implication gives 3h+1<=population(r), and
population(2r+1)=population(r)+1 gives the actual desired bound

```
exists L>0, q=Exp(width*L) and Radix(v) at this same L and
  3*(width*L)+2 <= population(rank(v)).
```

The phrase “Radix(v) at this same L” must be expanded into its actual
conjunction in Lean; do not existentially choose a second unrelated block
count. A natural-domain client may apply the accepted single shift v+1 once.
No source31 witness, desired weight, binomial or norm oracle belongs in either
public zero-to-population endpoint.

Recommended order: represented power plus complete integer Pell sandwich;
represented Pascal/factorial arithmetic plus full binomial extraction;
odd factorial parts plus the one-sided central population theorem; then the
actual current-zero composition. The binomial/factorial work is substantial
and presently open. The path is finitary and compatible with genuine IΣ1
induction, but this note does not establish its Lean elaboration or a literal
closed PA/HA derivation. Native word/carry/tableau soundness, the outer
simultaneous converse witnesses and the final HA equation equivalence remain
separate. No new compiler or cache union is authorized by this proposal.

## Source and cache scope

The adjacent source inventory hashes the exact files consulted, including
accepted CarrierRadix ROOT provenance and the explicitly provisional
BinaryPopulation source. It is a source audit, not a fresh object/provider
authentication. PRF, Seq, Exponential and Ring are already present in the
accepted Pell lineage; a power/Pell comparison leaf appears to require no new
Foundation module. Exact imports, reachable union, companion qualification and
accepted providers must nevertheless be separately frozen and reviewed before
any implementation/build. The later Pascal/factorial and population pairs
will add new custom leaves; an exact count cannot honestly be fixed before
their interfaces and accepted population provider exist.
