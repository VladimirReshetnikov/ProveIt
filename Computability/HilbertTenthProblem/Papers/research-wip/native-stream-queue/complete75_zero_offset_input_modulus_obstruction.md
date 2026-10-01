# The free modulus a gives a sparse-input obstruction, not an 88/135 improvement

Replacing the input modulus `Delta=(a+2)^2-1` by the already computed
quantity `a` changes only one multiplication in
[coupled88](complete75_coupled_index_linear88.md). The resulting literal
polynomial still costs **88=47M+41A**, has nineteen positive supplied
witnesses, and has exact degree **135**. It is **not** a universal
successor: for every fixed admissible compiler tuple, every positive
zero must satisfy

    2d*x+b=psi_2(v) for some positive odd integer v.       (1)

Here `psi_A(0)=0`, `psi_A(1)=1` and
`psi_A(j+1)=2A*psi_A(j)-psi_A(j-1)`. Its parameter-two sequence begins
`0,1,4,15,56,209,...`. Condition (1) excludes infinitely many ordinary
positive inputs for every fixed d and b. In fact the modified projection
contains only O(log N) inputs at most N.

This is a proved input-projection obstruction, stronger than a failure
of an inherited coordinate map. It rules out this particular attempted
88/degree135 construction. It does not rule out other 88-operation
degree improvements, and it leaves the established **75 comparison /
88 polynomial** universal bounds unchanged. The valid
[linear-modulus89 construction](complete75_linear_input_modulus89.md)
pays one addition for `a+1`; that offset changes the recurrence modulo
the index modulus and is essential to its proof.

## 1. The exact altered circuit

Retain all fixed compiler conditions, including

    B=2^d, d>=4, 0<MC,MF<B-1,
    MC=2 mod4, MF=4 mod8, popcount(MC)+popcount(MF)=d,

and the original synchronization, transport and input layout. In
particular b is positive and odd, b<B, and x is the ordinary positive
input. All nineteen positive coordinates remain exactly those of
coupled88. Its full strong auxiliary equation and both positive ratio
slacks are unchanged.

Use its computed quantities

    q=(B-1)J+1, X=wq^3, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    A=a+2, H=4a+3, Delta=A^2-1,
    D=X+ac+(rho+sigma)H,
    C=q-F-Z-alpha-2d*x, W=C-Z, u=2d*x+b.

Replace only the input ordinate by

    kappa=u+delta*a, mu=W+a*kappa+rho*H.                 (2)

The output is the same eight-factor product minus one, with changed
input factor `N2=mu^2-Delta*kappa^2`. All seven other factors are
unchanged. There are no new equations or uncounted tests. In the actual
[source](complete75_zero_offset_input_modulus_obstruction.py), register
`A` contains Delta and `R12` contains a. Thus the only edited instruction is

    index_product=delta*A   ->   index_product=delta*R12.

The [receipt](complete75_zero_offset_input_modulus_obstruction.json)
records the complete acyclic DAG and the exact ledger:

    product certificate: 87=47M+40A, one comparison;
    polynomial output:  88=47M+41A, nineteen positive witnesses.

These are costs for the rejected candidate, not new universal bounds.
Computed expressions C, W and mu may be signed away from zeros.

## 2. Main recovery is independent of the changed congruence

Suppose a positive supplied tuple is a zero of the altered polynomial.
Every factor is an integer unit. Exactly as in
[linear-modulus89 Section 2](complete75_linear_input_modulus89.md#2-the-coupled-proof-still-restores-the-main-kernel),
the main coupled proof uses the input factor only to exclude its
negative sign modulo four. Its form is still a Pell norm with the
unchanged discriminant Delta, so this exclusion holds for any integer
kappa and mu. The proof does not use the defining congruence for kappa.

Consequently the unchanged ratio, strong-rank, signed-index and
compiler-mask arguments still force all eight factors to equal one.
They restore the full half-binomial kernel and give

    q=2^t, X=2^R, c=psi_A(R), D=chi_A(R),
    R=3 mod4, R>3q+1, q>=16.                          (3)

The positive transport equation gives C>0, hence `-q<W<q` and
`u=2d*x+b<2q<R<a`. No input index has been decoded at this point.
The inherited half-binomial ratio proof also supplies, with
`r0=(R-1)/2`, the strict bound

    a > X^(r0+1)/3 = 2^(R(R+1)/2)/3.                   (4)

This is [half-binomial42 Section 5](pell_kernel_half_binomial42.md#5-ratio-bounds-and-power-recovery),
equation (13), after its already established conclusion X=2^R. Using
it here does not invoke the changed input congruence.

## 3. The new congruence recovers a Pell value, not the index

Equation (2) makes kappa positive. Although mu was a signed expression
off zero, on this zero it satisfies

    mu > -q+a*kappa+rho*H > 0.

The positive Pell classification therefore gives v>=1 with

    kappa=psi_A(v), mu=chi_A(v).                        (5)

Let `E_A(j)=chi_A(j)-a*psi_A(j)`. Its initial values are 1 and 2, and
its positive successive differences increase under the Pell
recurrence. It is strictly increasing. From the supplied positive
rho,sigma and W<q<X,

    E_A(v)=W+rho*H < X+(rho+sigma)H=E_A(R).

Thus **v<R**. This reasoning uses neither W>0 nor the old omitted
positive difference c-kappa; it restores the index bound directly.

Reducing the recurrence modulo a now gives

    A=2 mod a,
    psi_A(j)=psi_2(j) mod a for every j>=0.             (6)

This differs from reduction modulo a+1, where the sequence becomes j.
Equations (2), (5) and (6) imply `u=psi_2(v) mod a`.

Both representatives are smaller than a. Already `0<u<2q<R<a`.
For the other one, the recurrence gives

    0<psi_2(v)<=4^(v-1)<=4^(R-2),
    3*4^(R-2)<2^(R(R+1)/2) for R>=7.                  (7)

The first inequality permits equality at v=1 and v=2. Its weak form
is sufficient: (3), (4) and the strict second inequality put
`psi_2(v)<a`. The congruence in (6) is therefore the exact equality

    u=psi_2(v).                                      (8)

Finally `psi_2(v)=v mod2` by recurrence. Since u is odd, v is odd.
This proves the full necessary condition (1).

The changed congruence itself does have positive quotient solutions:
for a>0 and v>=2, the integer

    (psi_(a+2)(v)-psi_2(v))/a

is positive by (6) and monotonicity in the Pell parameter. These local
fixtures show why congruence and positivity alone do not repair the
index. They are not claimed to satisfy the complete outer source.

## 4. Uniform sparse projection and explicit omitted inputs

The same recurrence gives `psi_2(v)>=2^(v-1)` for v>=1. For fixed
admissible d,b, if a positive zero has x<=N, (8) implies

    v<=1+floor(log2(2d*N+b)).

Each v determines at most one x. Hence the positive projection has
at most this many inputs in [1,N], and has density zero. It omits
infinitely many positive integers for every fixed compiler tuple.

There is also an explicit parameterized rejection family. Choose any
sufficiently large n with `psi_2(n)>=b` and
`psi_2(n+1)-psi_2(n)>2d`, and put

    x_n=floor((psi_2(n)-b)/(2d))+1.

Then x_n>0 and

    psi_2(n)<2d*x_n+b<psi_2(n+1).

The strict increase of the Pell sequence proves that this input is
not in its range and therefore has **no positive zero of the altered
full polynomial**. The gaps grow without bound, so this produces
arbitrarily large rejected inputs. The checker independently constructs
and tests such inputs; for example d=4,b=1,n=4 gives x=7 and u=57,
strictly between psi_2(4)=56 and psi_2(5)=209.

In particular no fixed admissible instance of this altered family can
represent the computably enumerable set of all positive integers.
The established original compiler can represent that set, so its
universal correctness theorem cannot be inherited by this rewrite.
This conclusion uses the parametric necessary-condition and rejection
proof, not a materialized giant accepting parent tuple. No specific
compiled universal alphabet or numerical all-input compiler instance
is supplied here. The exact modified accepted set inside (1) is not
determined; a converse to (1) is not claimed.

## 5. Exact arithmetic identities and degree

For arbitrary supplied integer assignments, write kappa_old and mu_old
for the coupled88 input expressions and set

    z=delta*(Delta-a).

The changed values satisfy

    kappa_new=kappa_old-z, mu_new=mu_old-a*z,
    N2_new-N2_old=2z*(Delta*kappa_old-a*mu_old)-H*z^2.  (9)

All other factors are identical. Multiplying (9) by their product
therefore gives an exact whole-polynomial correction identity without
dividing by any factor. The executable checks it and an independent
direct eight-factor formula on 512 assignments, including signed
supplied coordinates and negative computed input roots.

The exact cancellation

    N2=(W+rho*H)^2+2a*kappa*(W+rho*H)-H*kappa^2

gives the changed factor degree 26. Let

    Q=(B-1)J, k0=eta+zeta,
    Ctop=Q-F-Z-alpha-2d*x.

The highest input factor is

    4delta*(2rho-delta)*w^3*s^3*Q^18.

The eight factor degrees are `14,22,26,28,9,5,22,9`. Their product
has the nonzero degree-135 highest form

    32*(B-1)^87*h^2*(rho+sigma)*delta*(2rho-delta)
      *i^2*f^2*(eta+zeta)^8*w^11*s^18*J^87
      *Ctop*(2g-eta-zeta).

This is the same highest form as the valid 89-operation linear-modulus
packet; the missing constant offset is lower degree but changes the
input projection. Three exact weighted, offset polynomial evaluations
verify every factor degree and this highest coefficient. Additional
checks use independent two-by-two matrix powers for the Pell
congruence, representative bounds, omitted inputs and sparse counts.

Default execution recomputes and compares the deterministic receipt:

    python3 complete75_zero_offset_input_modulus_obstruction.py

Use `--write-receipt` only to regenerate it. The finite checks support
the parametric proof and are explicitly scoped to arithmetic identities
and necessary-condition fixtures; they do not assert full positive
accepting source tuples.

Independent review checked the literal one-gate rewrite, recovery order,
strict representative bounds, sparse-projection argument and exact
degree forms. A fresh default receipt replay passed.
