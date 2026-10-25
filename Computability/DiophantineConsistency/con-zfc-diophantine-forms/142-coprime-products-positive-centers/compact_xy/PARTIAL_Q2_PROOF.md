# Partial saturation: retain s/q until the final source step

This companion has ten strictly positive integer unknowns and the same entire
fixed coefficient tuple as `PROOF.md`. Its principal `bV` equation has
**80 binary arithmetic operations and exact degree 382**. The `V^2` companion
has 79 operations and degree 516; it is included for reproducibility, but is
dominated in both metrics by the 77/464 equation of `PROOF.md`.

The proof combines the XY carrier's signed root/transport argument with a
different order of divisibility recovery. It does not presume `q^3|Y` before
it is established. The earlier q-cube construction remains separately supplied.

## 1. Complete polynomial changes

Use all definitions and the ten inputs in `PROOF.md`, except set

    Y=q^2*s, E0=q^4, D1=q*E0=q^5,
    M=h*D1*H,
    Z=h*D1*[H*(n-L*B)+Kpos]-H*[D1*B+h*(e-s*E0)],
    RG=M^2*G,
    N=Q*(Z^2-RG*V^2)+(RG-Z^2).

Here `L=bV` for the principal equation and `L=V^2` for the companion.
The auxiliary input remains unshifted: `b=cT-R`. The definitions
`A=Y(X+1)+1`, `V0=XY^2`, `E=1+V0(V0+1)k^2`, and all strong/auxiliary
Pell quantities use this new `Y`. The DAG uses a helper `D=XY` in
`A-1=D+Y`, but its carrier denominator factor is `D1=q^5`, not this helper.

Every displayed quantity is polynomial. In particular `E0` is the polynomial
`q^4`, and no division gate is being hidden in the notation `D1/q`.
For proof only, define `sigma=s/q`, `rho=e/D1`, and the same
`kappa=Kpos/H`, `t=B/h`, `W=1+hL`. Then identically

    z=Z/M=n+kappa+sigma-W*t-rho.                 (1)

The positive fraction `sigma` is deliberately retained. It later enforces
the missing factor `q` in `s`; simply deleting it would not be justified.

## 2. Roots, sign, and rank before index authentication

Sections 2--4 of `PROOF.md` apply with the following explicit changes.
Now `Y>=q^2`, not `q^3`, but all unconditional bounds hold. Signed
product-square recovery gives `G=g^2`, positive integers `tau,f0,y`,
`z=epsilon*g*y`, and the doubled strong interface. The exact same
signed all-index folding yields `c=psi_A(p)` with odd `p`, and
`k=2psi_P0(n0)` with `P0=2XY^2+1`, `n0>=2`.
The lower bound is now

    k>=8XY^2+4>8q^5, c>kY>=k>8q^5.             (2)

In the third-main-index exclusion, the only size requirement was `Y^3>2`
and `Y(X-1)>2(X+1)`, both immediate. The contradiction `2Y-X` equals
one or two still applies because `q|Y` and `q|X` hold literally.
Thus `p>=5`, and both signed third auxiliary branches remain excluded.
Consequently `g*y<L/2` for both transport weights.

The new exact identity `e=b-cT+k-1<b` gives
`rho<b/D1<=|b|/D1`, with `D1>2`. If `B<=-1`, equation (1), positive
`kappa,sigma`, and `Wt<-L` give

    n=epsilon*g*y-kappa-sigma+Wt+rho
      <L/2-L+|b|/D1<0,

contradicting `n>0`. Thus `B>=0`, `C>0`, and the inherited mask
bound gives `3q<R<q^4-2`. Bound (2) gives `c>2R`; hence `b,V>0`.
The unchanged strong-rank and signed-index interfaces recover `p=R`,
odd `R`, even `q`, and odd `J`, exactly as in the q-cube proof.

## 3. Exact first index without assuming q divides s

Equation (1), or its literal cleared form, and the integrality of `z`
give

    D1 | hH*(e-sE0).

Now `Y=q^2s`, so

    E0=q^4, D1=q^5,
    q^4 | sE0, q^5 | D1,
    gcd(q,hH)=1,

the last because `h=q-1` and `H=4Y(X+1)-1=-1 mod q`.
Therefore `q^5 | e-sE0`, and in particular **`q^4|e`**.
This conclusion does not require `q|s`.

The first-Pell congruence gives `k=2n0 mod 4XY^2`. Since
`XY^2=w*q^5*s^2` is divisible by `q^5`,

    q^4 | 2n0-R-1.

Also `P0>A`, and `c>k`, so `1<=n0<R` by the same monotonicity
argument as before. Thus `|2n0-R-1|<R<q^4`. It follows that
`2n0=R+1`. Returning to the complete congruence gives `4XY^2|e`;
because `D1=q^5` divides `XY^2=w*q^5*s^2`, this implies

    4D1 | e, so rho=e/D1 is an integer.          (3)

The full denominator is recovered after the exact index, not by a false
coprimality assertion about `D1` and `hH`.

## 4. Projection, then the missing factor q in s

By (1) and (3), `kappa+s/q-Wt` is integral. Clearing through `qhH`
gives `H|qh*Kpos`. Since `H=-1 mod q`, this implies `H|h*Kpos`.
The parent's uniform ratio lemma at scale one, with the authenticated
first index, gives exactly the same strict whole-product bound. Its
projection therefore gives `X=2^R` and makes `kappa` integral.
Equation (1) now says

    s/q-WB/h is an integer.

Multiplication by `qh`, followed by reduction modulo `q`, shows `q|s`,
because `gcd(q,h)=1`. Reduction modulo `h` shows `h|B`, because
`W=1 mod h` and again `gcd(q,h)=1`. Consequently

    q^3 | Y=q^2s, and t=B/h is a nonnegative integer.   (4)

This is precisely the native divisibility omitted at the start. All
fixed-minus parity, exact half-binomial, and unscaled source reconstruction
lemmas now have their full hypotheses. The same entire indexed native
tuple decodes a finite syntactic ZFC refutation.

## 5. Canonical positive converse

A refutation supplies the parent's canonical `Y` with `q^3|Y`.
Choose the new positive input `s=Y/q^2`, so `sigma=s/q=Y/q^3` is an
integer. The scale-one first/main witnesses, fresh seed period, and doubled
strong pair are constructed as before. The canonical auxiliary witness
gives a positive unshifted `T=Tstar`, and positive `V,y`.
The first-index congruence gives `e` a positive multiple of `4D1`, hence
integral `rho>0`. Also `kappa` and `t>=0` are integral. The retained seed
growth estimates give `f0>kappa` and `tau>Y>=sigma`, and `f0,tau>=3`.
Thus `g=tau*f0>f0+tau>kappa+sigma`.

Set

    n=g*y+(1+hL)*t+rho-kappa-sigma.

This is a positive integer. Its carrier is exactly `z=g*y`, and the
literal equation vanishes. This completes both directions and hence the
same ordinary, ZFC-formalizable no-zero/Con(ZFC) equivalence. It does not
assert Con(ZFC) or provide a new object-ZFC certificate.

## 6. Counts and exact leading forms

Relative to the corresponding 76/626 or 77/464 unshifted q-cube graph:
remove the private `q^3` multiplication, add two arithmetic rows needed
to evaluate `E0=q^4=(q^2)^2` and `D1=qE0`, and add the two rows
`sE0=s*E0`, `eclear=e-sE0`. The net cost is three operations.
This gives **79/516** and **80/382**. All inputs, coefficient ports, and
rows remain live. No quotient operation is counted as free.

The relevant exact degrees are

    deg Q=102, deg V=97, deg G=64, deg M=11, deg B=2.

For `V^2`, `deg Z=207` and the unique dominant term `QZ^2` has
degree 516. For `bV`, `deg Z=115`, while the unique dominant term
`-QM^2GV^2` has degree 382. With `q0=beta J`, `k0=eta+zeta`, and
`C0=q0-F-alpha`, the full highest components are

    [N79]_516=2^14*q0^272*w^46*s^108*i^20*k0^64*T^4*C0^2,
    [N80]_382=-2^10*q0^206*w^34*s^80*i^14*k0^46*T^2.

They are nonzero for the actual positive coefficient `beta`. The verifier
collects the complete leading polynomials exactly (390 and 47 monomials),
checks every literal graph row and coefficient byte, and compares the DAG
with an independently written formula. The finite checks supplement the
unbounded proof above; they do not test consistency.
