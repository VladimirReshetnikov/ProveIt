# Monomial rescaling cannot shorten the first norm below five gates

Every nonzero monomial multiple of the first-norm polynomial still requires **at least three multiplications and two additions/subtractions** at its six existing paid inputs. Thus multiplying this factor by a nonvanishing monomial cannot produce a four-operation replacement within this interface. This extends the [exact first-norm component bound](first_norm_five_gate_lower_bound.md); it does not lower or establish optimality of the complete 84-operation universal polynomial.

The allowed inputs are

    T, X, Y, k, E=XY, Z=kY,

with T,X,Y,k algebraically independent. Binary addition, subtraction and multiplication, and fixed rational constants, are allowed. For every nonzero rational lambda and nonnegative integers a,b,c,d,e,f, the target is

    lambda * T^a X^b Y^c k^d E^e Z^f * P,
    P=T²−(EZ)(EZ+k)=T²−X²Y⁴k²−XY²k².                 (1)

The multiplier is a specified polynomial, **not an additional free input**. Each of the two lower bounds permits arbitrarily many operations of the other type. The bound is attained when the multiplier is one; no attainment claim is made for other multipliers.

## Multiplication bound for every monomial

The multiplier normalizes to

    lambda * T^a X^(b+e) Y^(c+e+f) k^(d+f).          (2)

Set Y=1. All six available inputs become affine in T,X,k, including the duplicate ports E=X and Z=k. Even with every affine combination free, two multiplication gates can produce degree at most four. The restricted target has degree

    4+a+b+e+d+f.                                     (3)

Its highest monomial has nonzero coefficient −lambda. If any of a,b,d,e,f is positive, (3) is greater than four, excluding two multiplications immediately.

The remaining case has multiplier lambda*Y^c. At Y=1 the target is a nonzero constant times

    R=T²−X²k²−Xk².                                  (4)

Here is the underlying quartic obstruction, including the dependent-port specialization. Grant arbitrary affine combinations for free and divide the target by lambda for free in this relaxed model. A two-product computation of (4) must have first product Q=A B, where A,B are affine, and final form

    h*(alpha Q+u)*(beta Q+v)+b0 Q+z,                 (5)

where h,alpha,beta are nonzero rational constants and u,v,z are affine. Otherwise it cannot have degree four. The top degree gives

    h alpha beta Q_2² = −X²k².

Unique factorization forces Q_2 proportional to Xk. Because Q itself is a product of affine forms, its two linear parts are proportional to X and k in some order. Therefore

    Q=q Xk+r X+s k+t, q!=0,                          (6)

with no T term. At X=0 the target is T² and Q becomes affine. The homogeneous quadratic part in (5) is the product of the two remaining linear forms; unique factorization forces both forms to be nonzero multiples of T. Consequently the total k coefficient in each operand vanishes:

    alpha*s+u_k=0, beta*s+v_k=0.

For general X, both second-product operands therefore have only Xk,X,T and constant terms. Their product has no Xk² term. Neither b0 Q nor z can supply that cubic term, contradicting its coefficient −1 in (4). This excludes two multiplications in the remaining case. Together with (3), it proves the multiplication bound for every multiplier in (1).

## Addition bound for every monomial

All six available inputs are monomials in the independent variables. With at most one addition/subtraction, every nonzero final result has the form

    scalar * monomial * binomial^n, n>=0.            (7)

Indeed, everything before the sole addition is a monomial. Afterwards multiplication only accumulates monomial factors and powers of that single binomial. This includes arbitrary squaring and reuse; a degenerate binomial only makes the output a monomial.

The polynomial P is irreducible in Q[T,X,Y,k]. Regard it as a monic quadratic in T with radicand

    (kY)² X(XY²+1).

The X-valuation of that radicand in Q(X,Y,k) is one, so it is not a square. The quadratic is irreducible over the fraction field, and monicity and Gauss's lemma give irreducibility in the polynomial ring. Moreover, no variable divides P, and P has exactly three nonzero monomials.

The target (1) has exactly one nonmonomial irreducible factor, P, with multiplicity one. Unique factorization in (7) therefore forces n=1 and the binomial itself to be a nonzero scalar times a monomial times P. That product has exactly three terms, a contradiction. Hence at least two additions/subtractions are necessary, independently of how many multiplication gates are allowed.

## Connection to the current complete source and limitations

The current [84-operation source](complete84_scaled_strong_output.md) computes this component using

    tau_square = tau_root*tau_root
    first_root_base = UM*ksn2
    first_next = first_root_base+R10b
    first_product = first_root_base*first_next
    norm_first = tau_square−first_product.

The paid identities are UM=wn2*sn2 and ksn2=R10b*sn2, so T=tau_root, X=wn2, Y=sn2, k=R10b give precisely the interface above. The five-row component costs 3M+2A. The rest of the complete source is unchanged.

On the positive integer domain every monomial in these six ports is nonzero. Thus monomial scaling is a legitimate potential zero-preserving operation when applied to an entire output. The theorem shows that this particular component cannot become cheaper than five gates by such scaling. It does **not** supply or count a transformed complete universal circuit: its other factors and final subtraction would also need correct treatment and fully paid arithmetic.

Additional paid registers, changed witness coordinates, rational-function multipliers, general nonmonomial positive multipliers, joint computations with other factors, and agreement only on a constrained zero set are outside the theorem. In particular the nonmonomial discriminant scaling that produced the 84-operation source is not excluded. The full universal bound remains 84 and the independent-gamma83 language remains unresolved.

## Executable evidence

The [fresh helper](first_norm_monomial_scaling_bound.py) authenticates five frozen predecessor files as bytes, reads their saved JSON as inert data, checks the full current 84-row source closure and liveness, and matches the literal first-norm and dependent producers. Exact sparse expansion gives (1) and the odd radicand valuation. It also checks the normalized multiplier and degree formula for all 729 six-port exponent choices from {0,1,2}; three use the quartic branch and 726 use the degree branch. These finite cases corroborate the formulas, while the quantified proofs above establish the unbounded theorem.

The helper neither imports nor executes any predecessor program. It emits a deterministic [receipt](first_norm_monomial_scaling_bound.json) carrying its own source digest and all five dependency pins. Duplicate JSON keys are rejected, and saved-receipt comparison is recursive and type-exact. Fresh normal and optimized exact replays from working directory `/` both passed:

```sh
python3 /absolute/path/first_norm_monomial_scaling_bound.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/first_norm_monomial_scaling_bound.json
python3 -O /absolute/path/first_norm_monomial_scaling_bound.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/first_norm_monomial_scaling_bound.json
```
