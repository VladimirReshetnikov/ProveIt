# The binary selector still needs its divisibility condition on X

Computing `X=r+bound_beta` from an already paid positive bound appears to
remove one multiplication, one equation and one positive witness from
the [standalone selector56](native_controller_binary_selector56.md).
It does not preserve the selector theorem. The modified system has a
strictly positive solution with **q=48**, although the original system
forces q to be a power of two.

This is a standalone typing obstruction. It does not establish a false
accepted input for the joined matrix compiler, whose stronger outer
identity `q=16P^L` excludes this particular scale.

## 1. The exact proposed saving

The parent computes `X=wq` by one multiplication and separately compares
it to the paid addition `r+bound_beta`. Delete w and its multiplication,
redirect every X consumer to the bound expression, and delete this one
comparison. The candidate has **55=28M+27A**, thirteen comparisons and
eighteen positive auxiliary witnesses. Its ordinary sum of squares has
**93=41M+52A**, versus the parent's 97-operation SOS.

All other equations remain, including both positive ratio slacks, the
strong auxiliary equation, the fixed-minus congruences, the positive
four-field packing and checksum, and the odd quotient Y/q. The
[literal source](native_binary_X_divisibility_obstruction.py) verifies
all thirteen retained residuals against the parent after the formal
substitution `w=(r+bound_beta)/q`. This rational substitution identifies
the exact lost requirement: w need no longer be an integer.

## 2. Explicit outer data at a forbidden scale

Take

    q=48, (F0,F1,F2,F3)=(17,5,23,2),
    r=F0+qF1+q^2F2+q^3F3=274433
     =1+2^12+2^13+2^18.

All four fields are strictly positive, their sum is q-1, and r is odd
with popcount four. Set

    J=2r+1, X=2^J,
    Y=floor((X+1)^(2r)/X^r)
     =sum_(j=0)^r binom(2r,r+j) X^j.                 (1)

The standard binomial expansion gives (1), since the omitted fractional
tail is below 1/4. Every noncentral term is divisible by X. Thus

    v2(Y)=v2(binom(2r,r))=popcount(r)=4.             (2)

Also X=-1 modulo3. Pairing symmetric coefficients in `(1-1)^(2r)=0`
gives the exact integer identity

    sum_(j=0)^r (-1)^j binom(2r,r+j)=binom(2r,r)/2.

Consequently Y equals the right side modulo3. Legendre's factorial
valuation formula gives

    v3(binom(548866,274433))=7,

so 3 divides Y. Together with (2), this proves that `s=Y/48` is an odd
integer. It is greater than one, because `Y>=X^r>48`. Hence the new
supplied values

    bound_beta=X-r, s=Y/48, odd_half=(s-1)/2

are strictly positive integers. They satisfy the retained outer bound
and odd quotient equations. But 3 does not divide X, so no positive
integer w can restore `X=wq`.

## 3. The retained Pell coordinates really extend these data

Apply the same positive odd-index kernel construction as in the parent
selector converse. Its core depends on X,Y,r; the scale q enters only
through the outer quotient definitions. Those definitions now require
the integral s proved above, and no w coordinate remains.

More explicitly, set

    a=Y(X+1), A=a+2, Delta=A^2-1, P=2XY^2+1, E=XY,
    k=psi_P(r+1), c=psi_A(J), d=chi_A(J),
    tau=(chi_P(r+1)-1)/2,
    eta=c-Yk, zeta=k-eta,
    h=(k-r-1)/E, ga=(d-X-ac)/(4a+3).

The parent's converse estimates apply at this same odd r and exact
rounded Y. They give `Y<c/k<Y+1`, so eta,zeta are positive. Its Pell
polynomial congruences make tau,h,ga integers; growth makes each
strictly positive. The exponent congruence uses the actual `X=2^J`
and does not require q to divide X.

For completeness, the usual fixed-minus auxiliary extension can be
chosen with index `m_aux=2cJ`. Put

    f=chi_A(m_aux), v=psi_A(m_aux),
    i=Delta*v/c^2, T=Delta*v,
    y_aux=psi_T(J), U=chi_T(J)/T,
    j=(U+J)/c, o=(U+c)/f.

The retained positive construction proves these are positive integers.
Here `J=3 mod4` gives both minus congruences, `c^2` divides v, and
the two Pell norms give the strong equation and the auxiliary norm.
These are precisely the retained core coordinates; they are fresh
values at the displayed r,X,Y. Thus the candidate has an actual
positive integer solution at q=48, rather than merely passing an
outer necessary condition.

The original selector's soundness proof recovers `X=2^(2r+1)` first
and then uses **q divides X** to conclude that q is dyadic. The
counterexample shows that the remaining odd valuation of Y and
positive packing checksum do not replace that step.

## 4. Evidence and scope

The [receipt](native_binary_X_divisibility_obstruction.json) audits the
literal 55-operation schedule and all thirteen symbolic residual
identities. It computes the actual central binomial coefficient at
r=274433 and checks its exact 2- and 3-adic valuations. Sixty-four
smaller exact instances independently check the rounding expression,
alternating-half identity and Y valuation.

The full astronomical Pell tuple is not materialized. Its existence
is the parametric positive extension just given, using the same retained
kernel converse as the complete selector. This packet rejects this
specific standalone shortcut. It neither claims a lower universal
bound nor rules out a new proof exploiting additional joined-interface
conditions.

Independent proof/source/default review passed. Ten further exact
quadratic-ring auxiliary constructions checked positive integral i,j,o,
the strong equation, auxiliary norm and both minus congruences. These
additional checks exercise the auxiliary map only; they do not
materialize the full q=48 counterexample tuple.
