# Independent gamma in the actual scaled-strong circuit: an unresolved 83-operation scout

The [source](complete83_independent_gamma_scout.py) and [receipt](complete83_independent_gamma_scout.json) save one complete **83=47M+36A** polynomial with **18 strictly positive witnesses**, ordinary positive input and exact total degree **187** on each inherited valid fixed-program numeral slice. It deletes the private addition `gamma_sum=rho+sigma` from the actual [universal84 source](complete84_scaled_strong_output.md), using the supplied positive `sigma` as an independent main quotient gamma instead.

**The ordinary-input language of this relaxation is unresolved. This is not a new universal operation bound.** Its literal positive inverse fails on infinitely many full zeros above every positive parent zero, even at the same valid compiler input. That failure does not establish a false input. The retained factors still recover the native index and history data; the exact remaining input obstruction is a multiplicative-order compatibility condition, described below.

This is distinct from the historical [independent-gamma87 relaxation](complete75_independent_gamma87_alias.md), which had nineteen witnesses and a different auxiliary block. It is also distinct from the refuted free-coefficient83 and outer-slack83 charts. This scout preserves the actual84 strong-rank restrictions, auxiliary quotient, original outer bound and all six compiler numeral recipes. In particular none of those other charts' all-input families is transferred here.

## 1. Literal source, full pullback and degree

The only deleted row is

    gamma_sum = rho + sigma.

Its sole consumer changes from `gam=gamma_sum*a4m5` to `gam=sigma*a4m5`. Every other producer and the full finalizer are retained. Write gamma for the new meaning of the supplied sigma port. The main and input roots become

    D = X + a*c + gamma*H,
    kappa = u + delta*Delta,
    mu = W + a*kappa + rho*H,
    H=4a+3, u=2d*x+b, Delta=(a+1)(a+3).

Here `a=R12`, `c=R10a` and `Delta=A` in the literal source. The Pell parameter is a+2; the source register A is the discriminant. The positive input-modulus witness delta is distinct from Delta.

Over every commutative ring the full outputs satisfy

    P83_gamma(gamma) = P84(sigma_old=gamma-rho).          (1)

The single exceptional induction premise is `rho+(gamma-rho)=gamma`; after that equality, all retained source rows agree inductively. Conversely the substitution `gamma=rho+sigma_old` recovers P84 on every assignment. It sends each positive parent zero to a positive child zero with all other supplied coordinates unchanged. The signed inverse in (1) is not a positive inverse on all zeros.

All 83 gates, all eighteen witness ports, x and the six fixed numeral ports are live. The complete ledger is

| Part | M | A | Total |
|---|---:|---:|---:|
| Seven-factor producer core | 41 | 35 | 76 |
| Six product multiplications and final subtraction of Delta | 6 | 1 | 7 |
| Full polynomial | 47 | 36 | 83 |

The coefficient recipes, including the already shifted MF source port, are unchanged. Every retained factor, loader and final subtraction is charged; the changed dominance domain is analyzed separately.

The pullback is an invertible linear change in two supplied degree-one coordinates, rho and sigma. It therefore preserves exact total degree on every fixed numeral slice. The parent's exact degree187 gives exact degree187 here; this uses no zero equation or positivity substitution. More explicitly, with

    Q=(B-1)J, k=eta+zeta,
    C1=Q-F-Z-alpha-2d*x,
    Nt_top=w*C1-transport_quotient*Q,

its leading homogeneous form is

    32 Q^111 h gamma delta^2 i^4 k^13 w^18 s^31
       * Nt_top * T^2 * f^2.                            (2)

T is the positive auxiliary quotient. The monomial obtained by choosing gamma, eta^13 and the term `-transport_quotient*Q` has coefficient `-32*(B-1)^112`, nonzero for every valid compiler. The seven factor degrees remain 22,18,32,60,7,2,46. The separate gate recurrence gives the naive upper bound197.

## 2. What still follows at every positive child zero

The all-ring scaled identity used in the parent remains valid after the same gamma substitution: the new output is Delta times the corresponding independent-gamma normalized85 product-minus-one. Before imposing an equation, positive q,w,s imply

    X=wq>0, Y=sq^3>0, a=Y(X+1)>0, Delta>0.

Thus every positive zero gives seven integer units in that normalized product. One must cancel Delta here; one cannot infer seven unit factors directly from the scaled product equaling Delta.

The local proof in the pinned [normalized85 mathematical review](review_complete85_auxiliary_bezout_math.md) uses gamma only to make D positive. Its pretyping, auxiliary positivity, normalized rank, step-down and index-sign arguments do not require gamma>rho or a decoded input. They therefore apply unchanged up to, but not including, the final invocation of the complete parent theorem:

* Modulo-four exclusions and the first-norm descent make the five normalized norm factors +1. Initially the index and transport factors are the same unknown sign.
* The actual transport equation and positive transport quotient imply C>=0 and F+Z<q, using the retained original definition `C=q-F-Z-alpha-2d*x`. Consequently -q<W=C-Z<q. The shifted packing gives positive R and R+2<q^4<=XY.
* The strong equation gives `f^2=1+Delta*i^2*c^4`. Its root-gap argument makes the computed V positive and restores positive auxiliary coordinates without invoking parent soundness.
* First/main Pell classification, normalized rank and the two auxiliary congruences identify the main index p=R. The ratio inequality then fixes the index and transport signs at +1 and gives first index `2n=R+1`.

The native-only asymmetric kernel proof in the pinned [scaling review](review_complete74_asymmetric_scale_math.md#2-the-precise-kernel-lemma-available-before-input-typing) likewise uses a positive gamma, not dominance over rho. Its local ratio/exponent argument recovers X=2^R and dyadic q, the native mask and index conclusions, and the genuine half-binomial Y. In particular the relevant bounds and parities are

    q=2^t>=16, R>=3q+1, R=3 mod4, X=2^R,
    a=Y(X+1)>q, A_Pell=a+2 even, Delta odd,
    H=4a+3 odd and divisible by3,
    u=2d*x+b positive and odd, -q<W<q.                 (3)

These are local kernel conclusions, not a declaration that the proposed ordinary input has been decoded. A native history with an unvalidated input marker is not promoted to acceptance at x.

The actual seven scaled factor values at a positive zero are therefore

    1,1,1,1,1,1,Delta.

The missing step is exactly the historical input-index comparison. Previously

    E_A(v)=W+rho*H < X+(rho+sigma_old)*H=E_A(R)

forced v<R. With independent gamma there is no such inequality. None is inferred from the parent theorem, because its strict positive sigma_old hypothesis is precisely what is in question.

## 3. Exact input-fiber criterion, including both parity branches

Fix any positive assignment to the other sixteen witness coordinates, including independent gamma, and fix x and valid compiler numerals. Suppose the six noninput factors have their intended values (five +1 and the scaled strong factor Delta), with the native bounds and parities (3). This need not be a parent zero or a canonical native fiber. Every positive child zero has such outer data by Section2.

The remaining full-output equation is exactly

    mu^2-Delta*kappa^2=1,
    kappa=u+delta*Delta,
    mu=W+a*kappa+rho*H,                delta,rho>0.      (4)

Already `mu>-q+a*kappa+rho*H>0`, so the positive Pell classification is legitimate. Write chi_A(v),psi_A(v) for the Pell pair at parameter A=A_Pell and positive index v, and `E_A(v)=chi_A(v)-a*psi_A(v)`. The recurrence gives

    E_A(v)=2^v mod H,
    psi_A(v)=v mod Delta      for odd v,
    psi_A(v)=A*v mod Delta    for even v.

Let

    O=ord_H(2),  g=gcd(2Delta,O).

Then (4) has positive integer delta,rho **if and only if** W modulo H belongs to the subgroup generated by2 and, for its discrete logarithm j modulo O,

    j=u mod g  OR  j=A*u mod g.                         (5)

This is an exact criterion for the full remaining input fiber, not a proposed inexpensive arithmetic implementation of discrete logarithms or orders.

For necessity, the odd branch gives `v=u mod 2Delta`. In the even branch multiplication by A inverts A modulo Delta, and parity gives `v=A*u mod 2Delta`. Combining with `v=j mod O` gives (5). Conversely CRT supplies arbitrarily large compatible v in either branch. Set

    delta=(psi_A(v)-u)/Delta,
    rho=(E_A(v)-W)/H.                                   (6)

They are integers. Taking v sufficiently large makes both strictly positive: psi_A(v)>=v and E_A(v)>2^v for v>=2. These observations prove positive completion, not just congruence solvability.

Because 3 divides H, O and g are even. The two branches are disjoint: W=2 mod3 selects the odd branch, W=1 mod3 selects the even branch, and W=0 mod3 is impossible. Smallness and positivity of an ordinary power marker are not assumed for the general criterion. The lower bound on mu is essential; a freely signed W with no bound would allow negative-root input norms and would not have this characterization.

## 4. Exact parent-history aliases and full inverse failure

Take any genuine positive parent84 zero at ordinary input x0, with

    u0=2d*x0+b, W=2^u0, 0<u0<R,
    gamma=rho_old+sigma_old=(E_A(R)-2^R)/H.

For a new positive ordinary input x, keep all other outer/main/auxiliary coordinates fixed except

    alpha_new=alpha_old+2d*(x0-x).                       (7)

Require alpha_new>0. This preserves C, W, the packed R and all six noninput factors. The input delta and rho may now vary independently because gamma has its own supplied port. Although some intermediate alpha/input rows change, the noninput factor values remain identical.

Here W is an odd power of2, so only the odd branch of (5) remains. A positive completion exists exactly when

    g | 2d*(x-x0),
    equivalently  m_alias | (x-x0),
    m_alias=g/gcd(g,2d).                                (8)

Thus (7)-(8) are necessary and sufficient for this fixed-history transfer in the actual83 source. They do not classify every possible outer history for a given x.

At x=x0 both conditions always hold. Choose the compatible v in (6) arbitrarily large, in particular v>R. Then

    rho-gamma=[E_A(v)-E_A(R)+2^R-2^u0]/H>0.              (9)

All eighteen supplied coordinates in the actual83 source remain strictly positive; all six noninput factors retain their parent values; the new input norm is +1; the complete output vanishes. This constructs infinitely many full positive zeros above every genuine parent zero, on the same valid compiler slice and ordinary input, with the signed inverse `sigma_old=gamma-rho` strictly negative.

Equation (9) is a full-zero existence theorem, not merely a freely chosen small Pell component. It uses existence of the given parent zero and exact Pell/CRT completion; this packet does not materialize an enormous complete native Pell tuple. It refutes this literal positive inverse on the whole zero set. Because the ordinary input is unchanged and accepted by assumption, it does **not** refute the proposed input language or rule out some different positive normalization.

## 5. The remaining language question is not removed by the new auxiliary block

A false-input theorem from (8) still needs an actual accepted native history and a rejected x with positive (7) and compatible (8). The historical [exact period analysis](complete75_independent_gamma87_period.md) and [compiler order filters](complete75_gamma87_compiler_order_filters.md) remain relevant and are pinned here. They provide local obstructions and conditional small-period classes, not such a history.

In particular, the native first/main restrictions force

    Y=(sum_(j=0)^((R-1)/2) binom(R-1,(R-1)/2+j)*X^j)/2,
    X=2^R, H=4Y(X+1)+3.

Y and H cannot be chosen freely while retaining these factors. The sufficient class H=3p with p prime would make the relevant gcd small, but no occurrence for a complete valid compiler history is proved here. The prime-modulus choice in the refuted free-coefficient83 construction used the loss of the native rank condition, and cannot simply be imposed in this source. Likewise the negative-index all-input construction for outer-slack83 uses an outer bound that this source retains unchanged.

No uniform bound excluding (8), no language-preserving normalization of all fibers, and no valid-compiler false-input history has been established. The strengthened source record makes the current18-witness question precise but does not resolve the historical mathematical obstruction. The established universal84 bound is not changed by this scout.

## 6. Bounded reproducible evidence

The standard-library helper pins twelve immediate source/proof files and reads them only as bytes or JSON. It executes no predecessor Python, archived program, compiler builder or historical suite. It emits the complete83 array with every supplied port and full paid finalizer.

It checks the private consumer and the inductive whole-DAG pullback, all gates/free-port liveness, 48 complete signed/rational assignments and 3,984 retained-register equalities. It also checks the private rho/delta consumers and their absence from every noninput factor, then verifies 216 noninput factor/outer-value equalities under 24 signed input/alpha shifts preserving C. Two full dense coefficient evaluations confirm the full pullback, factor degrees and degree187 at diagnostic numeral assignments; these supplement the uniform invertible-linear proof rather than certify the diagnostic numerals as compiler data.

Independent direct modular Pell recurrences cover complete joint periods for eight small even a divisible by6 and compare all H residues at six odd input values with both CRT branches. Sixteen strictly positive input components include both parity branches and negative representatives of W. They are input-component diagnostics only. They do not provide full compiler zeros or false accepted inputs.

From any working directory:

    python3 complete83_independent_gamma_scout.py --root /absolute/path/native-stream-queue --expect /absolute/path/complete83_independent_gamma_scout.json

`--output PATH` writes the deterministic receipt. Checks use explicit exceptions and recursively type-exact JSON comparison in normal and optimized Python. Fresh normal and `python3 -O` exact receipt replays from `/` pass. No frozen predecessor or repository file is changed.
