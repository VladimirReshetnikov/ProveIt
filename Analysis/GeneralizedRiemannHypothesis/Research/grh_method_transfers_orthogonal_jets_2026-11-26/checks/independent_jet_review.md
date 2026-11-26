# Independent review: Lubin--Tate inverse poles modulo pi^r

## Verdict

The proposed improved bound and equality criterion are correct in the standard Lubin--Tate coordinate `[pi](X)=pi X+X^q`. No counterexample arose in 210 exact finite Laurent-series calculations over Z/p^r, including q=p^f with f>1. The proof below works for every DVR of characteristic zero, arbitrary ramification e=v_pi(p), and q the residue cardinality.

The statement is sharper than the preceding report's general-coordinate estimate. For largest contact depth A>1 and r>1 the preceding coarse upper bound can never be attained in this standard coordinate. For A=1 the sharpness issue is exactly a binomial-carry condition.

## Setup and invariance under units

Let O be a DVR, pi its uniformizer, residue characteristic p and residue size q. Write `F_a=[pi^a]`, so `F_0=X` and `F_a=pi F_{a-1}+F_{a-1}^q`. Let `a_1,...,a_s` be the contacts `v_pi(b-c)` of one branch b with the other branches. Set

- `W=sum_i q^{a_i}`;
- `A=max_i a_i`;
- `m=#{i:a_i=A}`;
- `lambda=(q-1)q^{A-1}` when A>=1.

The formal-group relation gives `[b](X)-[c](X)=[b-c](X) U_{bc}(X)` with `U_{bc}` a unit of O[[X]]. Indeed `F(U,V)-U` is V times a unit whose constant term is one. If b-c=pi^a v with v a unit, `[b-c]=[v](F_a)=F_a V(X)`, where V has unit constant term v. Consequently the interpolation denominator Delta_b is a unit times `prod_i F_{a_i}`.

Multiplication by a power-series unit preserves the smallest exponent of a nonzero Laurent series over O/pi^r: the coefficient at that smallest exponent is multiplied by the unit constant term. This remains true despite zero divisors. Thus unit associates have the same inverse pole t_b. No assumption that the leading coefficient is a non-zero-divisor is needed.

## Newton-face lemma

For a>=1 let `lambda_a=(q-1)q^{a-1}` and write `F_a=sum_j c_{a,j}X^j`. Then:

1. F_a is monic of degree q^a and reduces to X^{q^a} modulo pi.
2. Every nonzero lower coefficient satisfies

   `q^a-j <= v_pi(c_{a,j}) lambda_a`.

3. Equality occurs exactly at `j=q^{a-1}`, where `v_pi(c_{a,j})=1` and `c_{a,j}/pi=1 mod pi`.

The leading monomial is the additional face term of valuation zero. Thus the lower face is exactly `X^{q^a}+pi X^{q^{a-1}}`, with the coefficient pi interpreted modulo pi^2.

**Proof.** The case a=1 is immediate. For a>1 use `F_a=pi F_{a-1}+F_{a-1}^q` and `lambda_a=q lambda_{a-1}`. A nonleading product monomial from `F_{a-1}^q` has total coefficient valuation K>=1 and degree deficit at most `K lambda_{a-1}<K lambda_a`, so lies strictly above the claimed face. A monomial `pi c_j X^j` from the first summand has valuation `1+k`, where k=v_pi(c_j), and deficit

`q^a-j=lambda_a+(q^{a-1}-j) <= lambda_a+k lambda_{a-1}`.

If k>0 this is strictly less than `(1+k)lambda_a`. If k=0 it is the leading term of F_{a-1}, giving `pi X^{q^{a-1}}` on the face. When contributions to the same coefficient are added, their valuations can only increase. At the unique claimed face exponent every contribution from the qth power has valuation at least two, so the coefficient remains pi modulo pi^2. This proves all assertions.

Note the lemma is about actual pi-adic valuations, not a chosen expression as a polynomial in pi. It therefore handles ramified coefficient rings without ambiguity from relations such as p=unit*pi^e.

## Sharp improved bound and equality criterion

For r>=1, let t_b be the largest inverse pole of Delta_b in `(O/pi^r)((X))`. If A=0 then t_b=W. If A>=1 then

`t_b <= W+(r-1)lambda`,

with equality exactly when

`binom(m+r-2,r-1) != 0 mod p`.

Equivalently, adding m-1 to r-1 in base p involves no carry. For r=1 the criterion holds automatically.

**Proof.** Write `F_a=X^{q^a}(1+G_a)` for a>=1. Every coefficient of the negative-power Laurent polynomial G_a is divisible by pi, so G_a is nilpotent modulo pi^r. Its inverse is the finite geometric sum `sum_{k=0}^{r-1}(-G_a)^k`. At the common slope lambda=lambda_A every monomial with coefficient valuation k has degree at least -k lambda. For a<A this inequality is strict for every nonconstant term; for a=A the unique face term is `pi X^{-lambda}`. Hence no term of the product inverse can have degree below `-W-(r-1)lambda`.

At exactly that extreme degree all surviving terms must have total coefficient valuation r-1 and must be assembled entirely from face terms of the m maximal-depth factors. Their generating expression is

`X^{-W}(1+pi X^{-lambda})^{-m}`.

Therefore the coefficient at the extreme exponent is congruent modulo pi^r to

`(-1)^{r-1} binom(m+r-2,r-1) pi^{r-1}`.

It is nonzero precisely when the binomial coefficient is a residue-field unit, equivalently not divisible by p. Lucas's theorem gives the carry-free criterion. All remaining contributions at that exponent have valuation at least r and vanish. The unit factor relating Delta_b to the product preserves the pole, as proved above.

This provides an exact criterion for attaining the improved bound; it does not give the entire lower pole when the extreme binomial vanishes. Other Newton faces can then matter.

## Comparison with the old bound

The previous report gave `W+(r-1)(q^A-1)`. For A>1,

`lambda=q^A-q^{A-1}<q^A-1`.

Thus the old bound is strictly too large whenever A>1 and r>1. For A=1 the two bounds coincide and the binomial criterion decides sharpness. For two branches, m=1, the binomial coefficient is one for every r, so the improved bound is exact even for A>1:

`t_b=q^A+(r-1)(q-1)q^{A-1}`.

This last formula is a particularly clean new explicit resolution of the two-branch higher-contact case.

## Exact formula for all r when contacts have depths zero or one

Suppose all a_i are zero or one and at least one equals one. Set `m=#{i:a_i=1}`, `e=v_pi(p)`, `lambda=q-1`. There is now no lower face to obscure the answer because

`prod_i F_{a_i}=X^W(1+pi X^{-lambda})^m`.

Consequently

`t_b=W+lambda K_m(r)`,

where

`K_m(r)=max{0<=k<r : k+e*v_p(binom(m+k-1,k))<r}`.

This is an exact finite formula, not merely an upper bound. The valuation of an ordinary integer in O is e times its p-adic valuation. Terms with k>=r vanish, and distinct k give distinct powers of X, so cancellation between different k is impossible.

### Optional: explicit eventual affine periodicity

This depth-one formula also gives a rigorously proved, if nonoptimal, period.

Let P be the least power of p with P>=m; let `d=m-1`, `L=floor((P-1)/e)`, `T=L+v_p(d!)+1`, and `Q=p^T`. Then for every integer r>=P,

`K_m(r+Q)=K_m(r)+Q`,

and hence `t_b(r+Q)=t_b(r)+(q-1)Q`.

**Proof.** For any k divisible by P, adding d<m<=P to k has no carries, so the binomial coefficient is a p-adic unit. Taking the largest multiple of P at most r-1 proves

`r-P <= K_m(r) <= r-1`.

For r>=P write `K_m(r)=r-1-delta(r)` with `0<=delta<P`. The admissibility of the candidate k=r-1-delta is equivalent to

`e*v_p(binom(d+k,d))<=delta`.

The threshold for the binomial valuation is at most L. Using

`binom(d+k,d)=prod_{i=1}^d(k+i)/d!`,

all such comparisons are determined by k modulo p^T: each factor's valuation truncated at T is determined by that residue, and if the numerator valuation reaches T it already exceeds every relevant threshold `L+v_p(d!)`. Thus the set of admissible deltas, and its minimum, are unchanged when r is replaced by r+Q. This proves the formula. The case m=1 has the simpler exact period one, with K_1(r)=r-1.

This periodicity statement is optional; the simpler exact finite maximum may be the clearest main presentation.

## Finite verification

I independently computed F_a recursively and performed finite geometric inversion modulo p^r using exact sparse Laurent polynomials. All 210 checks passed for:

- `(p,q)=(2,2),(2,4),(3,3),(3,9)`;
- contacts `(1)`, `(1,1)`, `(1,1,1)`, `(0,1,1)`, `(2)`, `(1,2)`, `(2,2)`, `(1,2,2)`, `(3)`;
- r=1,...,6; q=9 omitted the depth-three contact.

Some strict examples at r=4: for p=q=2, contacts (2,2), t=12 while the improved bound is 14; for p=2,q=4, contacts (2,2), t=56 while the improved bound is 68. These match the binomial criterion. Finite checks support the complete proof; they are not its justification.

## Presentation cautions

- State the standard coordinate hypothesis explicitly. Do not silently claim this sharper formula for arbitrary coordinates unless coordinate invariance is separately proved.
- The carry-free condition concerns the multiplicity m of the *maximal* contact depth, not the total number of competing branches.
- The equality criterion uses residue characteristic p, not q.
- For r=1 the carry statement is vacuous and always true.
- Branches with a_i=0 contribute X factors and hence W, but do not contribute to m when A>0.
- For one total branch there are no contacts, Delta=1 and t=0; treat that degenerate case separately rather than taking the maximum of an empty set.
- The proof verifies the local theorem and its relation to the preceding report. Historical novelty still requires a literature search.

## Review of exact threshold sharpness over nonreduced coefficients

The preceding report's componentwise threshold argument is sound over A=O/pi^r, with the following details made explicit.

1. The localization map A[[X]] to A((X)) is injective: multiplication by X is injective on formal power series even though A has nilpotents.
2. Each branch difference is a unit in A((X)), by its monomial-times-unit reduction and finite nilpotent geometric inversion. Lagrange interpolation over A((X)) therefore works as an identity over a commutative ring; a field is unnecessary.
3. P=prod_c(Y-u_c(X)) is monic in Y and distinguished over the complete Noetherian ring A[[X]]. Weierstrass division yields H=QP+R, with deg_Y R<d. Since each u_c lies in XA[[X]], P lies in (X,Y)^d, so H and R agree in all total degrees below d.
4. If branch b is observed to order n_b>=1+t_b and its observation vanishes, H(X,u_b)/Delta_b belongs to XA[[X]]. Multiplication by P_b in (X,Y)^{d-1} proves the interpolation sum lies in (X,Y)^d.
5. By the minimality of t_b, the constant coefficient of g=X^{t_b}/Delta_b in A[[X]] is nonzero. Otherwise g would be divisible by X, contradicting minimality after using the localization injection. No stronger unit assertion is required.
6. H_b=gP_b has a nonzero coefficient g(0) at Y^{d-1}; it evaluates to X^{t_b} on b and zero on every other branch. Thus it is an exact obstruction whenever n_b<=t_b, independently of the precisions on the other branches.

Hence the exact common precision is 1+max_b t_b. The lower-bound witness is valid even when g(0) is nonzero nilpotent.

## Coordinate changes

There is also a simple coordinate-invariance observation. If h(X) is in XO[[X]] with unit linear coefficient, then substitution X->h(X) preserves the least Laurent exponent over A. Moreover h(U)-h(V)=(U-V)J(U,V), with J(0,0) a unit. Under simultaneous conjugation of the branches by h, their denominator is therefore a unit times the old denominator after an invertible coordinate substitution. Thus t_b is invariant under such a change of formal-group coordinate. If invoking the standard integral isomorphism theorem between Lubin--Tate formal O-modules for the same pi, the formulas extend to those isomorphic models. The report can avoid invoking this additional theorem by retaining the standard-coordinate hypothesis.

## Reproducible artifacts

The independent verifier is `grh_transfer_results/code/check_jets.py` and the actual successful output is `grh_transfer_results/checks/jet_checks.json`. The script also checks the full inverse identity, exact depth-one formula, strictness of the preceding coarse bound for A>1,r>1, and the highlighted q=3,m=2,r=3 example: inverse pole 8, exact precision 9, old coarse precision 11.
