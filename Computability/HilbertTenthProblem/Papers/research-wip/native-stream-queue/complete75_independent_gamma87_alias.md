# Independent main and input quotients: an unresolved 87-operation relaxation

Deleting the addition `gamma=rho+sigma` from
[coupled88](complete75_coupled_index_linear88.md), and using the positive
supplied sigma directly as gamma, gives a literal **87=47M+40A**
polynomial of degree **151**, with nineteen positive witnesses. Every
positive parent zero maps to a positive zero of this relaxation.

The reverse direction is not established. The removed inequality
`gamma>rho` supplied the input-index bound `v<R`. There is an exact
conditional CRT mechanism for positive input-Pell aliases once that
bound is absent. A fresh half-binomial main component at R=11 exhibits
the mechanism with all its main ratio coordinates positive.

**The example is not a full compiler zero:** R=11 is outside the
required range `R>=3q+1` with q>=16. This packet neither proves nor
refutes universal soundness of the full 87-operation relaxation. It
records its exact source, positive forward map and a specific obstacle
to simply reusing the old input proof. The established complete bounds
remain **75 comparison / 88 polynomial operations**.

## 1. The one-addition candidate and the exact coordinate identities

Keep all coupled88 compiler numerals, masks, arithmetic definitions and
positive witnesses. In particular both ratio slacks, the full strong
auxiliary factor, all transport and width arithmetic, and the ordinary
input x remain. Only the main Pell root changes:

    old: D=X+ac+(rho+sigma_old)H,
    new: D=X+ac+sigma_new*H,
    A=a+2, H=4a+3, Delta=A^2-1.

The input quantities are unchanged:

    u=2d*x+b, kappa=u+delta*Delta,
    mu=W+a*kappa+rho*H.

Delete `gamma_sum=rho+sigma` and redirect its sole consumer to sigma.
Every other gate is identical. The actual
[source](complete75_independent_gamma87_alias.py) and
[receipt](complete75_independent_gamma87_alias.json) audit the consumer,
acyclicity, single multiplication-operand change and full ledger:

    certificate:86=47M+39A, one product=1 comparison;
    polynomial: 87=47M+40A, nineteen positive witnesses.

The exact arithmetic identities, without any zero-set assumption, are

    new_source(sigma_new=rho+sigma_old)=old_source(sigma_old),
    new_source(sigma_new)=old_source(sigma_old=sigma_new-rho).    (1)

All surviving registers agree under the second identity, and so do the
complete output polynomials. The first map preserves positivity.
Consequently every parent positive zero gives a candidate positive
zero at the same ordinary input. The second identity permits a
nonpositive restored sigma_old, so it is not a positive inverse proof.
These coordinate maps are proof substitutions, not extra runtime gates.

The factor degrees remain `14,22,42,28,9,5,22,9`. The exact leading form
is the coupled88 form with `rho+sigma` replaced by sigma:

    -32*(B-1)^99*h^2*sigma*delta^2*i^2*f^2
      *(eta+zeta)^8*w^13*s^20*J^99
      *Ctop*(2g-eta-zeta),
    Ctop=(B-1)J-F-Z-alpha-2d*x.

It is a nonzero degree-151 polynomial. The number 87 is only a
candidate-source cost; it is not promoted to a universal bound.

## 2. What the unchanged positive-zero proof still gives

At a positive candidate zero, the coupled main/sign proof remains
available. Its first, main, input and auxiliary norms have the same
forms and cannot be negative units. It uses the main quotient only
through its positivity; sigma_new supplies that positivity. The ratio,
strong-rank, signed-index and mask-population arguments therefore still
restore all eight unit factors as one and the main kernel as

    q=2^t, X=2^R, c=psi_A(R), D=chi_A(R),
    R=3 mod4, R>=3q+1, D-ac=X+gamma*H,
    gamma=sigma_new>0.

These are the same dependencies audited in
[linear-modulus89 Section 2](complete75_linear_input_modulus89.md#2-the-coupled-proof-still-restores-the-main-kernel).
Neither proof stage compares gamma with rho.

The input norm and positive transport give kappa>0, `-q<W<q`, and
`mu=W+a*kappa+rho*H>0`. Hence some positive Pell index v satisfies

    kappa=psi_A(v), mu=chi_A(v).

Let `E_A(n)=chi_A(n)-a*psi_A(n)`. Its initial values are 1,2, it is
strictly increasing, and its recurrence gives `E_A(n)=2^n mod H`.
Thus every candidate positive zero has

    psi_A(v)=u mod Delta, W=2^v mod H.                    (2)

The first congruence is `v=u mod Delta` when v is odd and
`v*A=u mod Delta` when v is even. **Odd v is not automatic** after
deleting dominance. The construction below deliberately uses the odd
branch; no classification of all new branches is claimed.

The old proof had

    E_A(v)=W+rho*H < X+gamma*H=E_A(R),

because W<X and gamma>rho. With gamma and rho independent, this strict
inequality no longer follows. Knowing `u<2q<R` does not bound v from
the modular relation (2).

## 3. An exact conditional alias lemma

Fix positive a and put `A=a+2`, `Delta=A^2-1`, `H=4a+3`. Let R>=3 and
let u,j be positive odd integers below R. Suppose a positive integer
ell is a period of two modulo H and satisfies

    2^ell=1 mod H,
    gcd(2Delta,ell) divides u-j.                         (3)

There are then arbitrarily large positive odd v such that

    v=u mod 2Delta, v=j mod ell.                        (4)

This is the ordinary two-congruence CRT, followed by positive multiples
of `lcm(2Delta,ell)`. It does not require ell to be the least period.
Choose v>R and set

    W=2^j, kappa=psi_A(v), mu=chi_A(v),
    delta=(kappa-u)/Delta,
    rho=(E_A(v)-W)/H,
    gamma=(E_A(R)-2^R)/H.                              (5)

All three quotients are strictly positive integers. For delta,
odd-index reduction gives `psi_A(v)=v mod Delta`; also
`psi_A(v)>=v>u`. For rho and gamma, the recurrence modulo H proves
integrality. The same positive recurrence gives `E_A(n)>2^n` for n>=2,
so their numerators are positive. Finally strict increase and j<R<v give

    rho-gamma=[E_A(v)-E_A(R)+2^R-2^j]/H>0.              (6)

These definitions satisfy exactly

    kappa=u+delta*Delta,
    mu=W+a*kappa+rho*H,
    mu^2-Delta*kappa^2=1.

If j differs from u, the selected small power W is not `2^u`.
The inverse coordinate in (1) is negative by (6). Thus an argument
using only these Pell equations, positive gamma and rho, the two
modular relations and u,j<R cannot restore the old dominance or
the exact input index. This is a conditional component lemma, not a
claim that (3) occurs for a particular complete compiled history.

## 4. A fresh half-binomial main component

The alias condition occurs at genuine main/first-kernel parameters,
rather than only at a freely chosen Pell discriminant. Take

    R=11, r0=5, X=2^11=2048,
    Y=(sum_(j=0)^5 binom(10,5+j)*X^j)/2
      =18102552965105790,
    a=Y(X+1)=37092131025501763710,
    H=148368524102007054843,
    Delta=1375826184012990521323440496422680018943.

The verified period

    ell=12288046457816218188

satisfies `pow(2,ell,H)=1` and `gcd(2Delta,ell)=6`. No factorization or
minimal-order assertion is needed. Choose u=9,j=3. Here u is the
ordinary input expression at d=4,b=1,x=1. One CRT representative is

    v=7519481144310636810215582595978389212779472456061533568031.

The checker verifies both congruences (4) and `pow(2,v,H)=8=2^j`.
It also evaluates the input Pell recurrence modulo Delta and H by
binary matrix powers; it does not expand the enormous full powers.
Equations (5)-(6) give positive delta,rho and rho>gamma exactly.

For the main component put

    Pfirst=2XY^2+1,
    k=2psi_Pfirst(6), tau=chi_Pfirst(6),
    c=psi_A(11), D=chi_A(11), g=tau-XY^2*k,
    eta=c-kY, zeta=k-eta,
    h=(k-12)/(XY), gamma=(D-X-ac)/H.

All these integers are materialized in the checker. Both norm
equations, both positive ratio slacks, the index quotient and the
main exponent quotient hold exactly; in particular
`g,eta,zeta,h,gamma>0` and `c>A*Delta^2`.

The remaining strong auxiliary component can be supplied by the
retained [canonical minus construction, half-binomial42 Section 6](pell_kernel_half_binomial42.md#6-exact-valuation-and-the-positive-converse):

    m_aux=2cR, f=chi_A(m_aux), T=Delta*psi_A(m_aux), i=T/c^2,
    y=psi_T(R), V=chi_T(R)/T,
    o=(V+c)/f, j_aux=(V+R)/c.

Its divisibility and minus congruences apply at these fresh parameters
with R=3 mod4 and give positive integral auxiliary coordinates.
They retain the full equation `(ic^2)^2=Delta(f^2-1)`.
These huge auxiliary powers are specified parametrically and are not
claimed as numeric fixtures.

This component uses scale D0=1. **It cannot be the full87 source tuple:**
the complete compiler requires q>=16 and R>=3q+1>=49, whereas R=11.
Its packed mask, transport and positive width equations have not been
instantiated. In particular no rejected input of the full compiler,
no full87 positive zero, and no failure of universal soundness is
deduced from this example. It only demonstrates the missing bound
with actual first/main ratio data and a compatible strong extension.

## 5. Evidence and the remaining question

The checker audits the sole deleted register and redirected consumer,
512 signed inverse identities on every surviving register, and 512
forward complete-factor/polynomial identities. Three weighted-offset
polynomial evaluations verify all eight factor degrees and the stated
degree-151 highest form. It also materializes small positive alias
components and checks the fresh R=11 main component and the large CRT
representative through exact modular arithmetic.

Run normally to compare the deterministic receipt, or use
`--write-receipt` to regenerate it. No parent file is changed.

To promote or reject the full87 candidate, one must still analyze the
aliases on actual packed compiler histories with q>=16, the complete
mask contract, and the positive ordinary-input width. A bound preventing
the aliases, a positive normalization preserving the same input, or a
full compatible false-input construction would settle that next step.
This packet supplies none of those missing conclusions and makes no
general arithmetic lower-bound claim.

Independent review checked the exact source substitution, positive
forward map, odd/even index distinction, conditional CRT proof and
the stated failure of the R=11 component to meet full compiler bounds.
A separate fresh default replay passed. The full87 candidate remains
unresolved; this review does not assert a complete false-input witness.
