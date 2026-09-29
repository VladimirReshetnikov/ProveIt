# Bounded rewrites of the complete 76-operation input bridge

This is a local, nonpublication research receipt over the actual frozen
`../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md` and
`../../verification/explore_fixed_raw_universal_76.py` at HEAD `50eea4d`.
It obtains **no 75-operation certificate**. The complete source expansions
and primitive lists are in `explore_complete76_bridge_rewrites.py/.json`.
No published source was changed, and no bound was omitted.

Write a for the supplied main parameter, D=a^2+4a+3, H=4a+3,
X=w*q^3, Lambda=q^2, and u=2d*x+b. The retained input interface is

    kappa=u+delta*D,
    c=kappa+phi,
    mu^2=1+D*kappa^2,
    mu=W+a*kappa+rho*H,
    C=Z+W.

The 14 bridge instructions include the scaling and strengthened raw bound.
Together the original input norm and exponent projection use 8 operations:
5M+3A. The already charged marker relation uses one further addition.
D, H, the main root square d_main^2, and Lambda-1 are available from
other parts of the complete schedule; their costs are never charged twice.

## 1. A coherent endpoint/root translation ties 76

Supply

    m=mu+1, V=W+1, T=Z-1

instead of mu,W,Z. Keep every other coordinate. The changed equations are

    m(m-2)=D*kappa^2,
    m=V+a*kappa+rho*H,
    C=T+V,
    r=[(Lambda-1)-(T+qF)](Lambda-1)+(MC+qMF)J.

The last identity follows from Lambda-Z-qF=Lambda-1-T-qF.
In particular, the translated packing needs no fresh Lambda+1 register.
Move the existing `Lm1=Lambda-1` before the gap instruction and use it
in both factors. Replace `mu*mu` and `D*kappa^2+1` by the subtraction
`m-2` and product `m*(m-2)`. Every other primitive is just a coordinate
rename. The exact source remains **76=41M+35A**, 30 positive coordinates,
19 equations, with all 19 residuals and the inherited auxiliary norm
correction verified symbolically.

The translated positive domain is sound, although restoration of the old
endpoint is not immediate before the kernel. Positivity gives
T+1<=C<q and 0<=V-1<q. These weak endpoint bounds suffice for the original
pre-kernel packing estimates: the actual masked field is Z=T+1 and is
strictly between zero and q. The norm m(m-2)=D*kappa^2>0 forces m>2,
so the restored mu=m-1 is positive. The retained gap and index equation
then recover the original odd input index. The bounded exponential
congruence forces V-1=2^u>0, excluding V=1. Thus the old W is strictly
positive and every old equation is restored.

Conversely every complete old solution has Z>1. Its decoded word has
N>2x>=2 occupied cells; removing the one End selector still leaves the
origin Start bit and a nonzero bit in another cell. Hence T=Z-1>0.
The three translations preserve every other witness and the exact packed
r and main Pell auxiliaries. This is an equivalent complete 76 source,
not a saving and not a weaker bound deletion.

The useful detail for future changes is that the norm's explicit +1 can
be moved into the root/marker coordinates at no net cost. It does not
remove the one addition: the norm now pays m-2 instead.

## 2. The positive projection difference costs 77

Supply V=mu-a*kappa instead of mu. The old projection itself proves V>0,
and mu=V+a*kappa is positive in the inverse map. The exact equations become

    V=W+rho*H,
    V(V+2a*kappa)=H*kappa^2+1.

The norm identity is exact because D=a^2+H. The four products are
`a*kappa`, `V*(V+2a*kappa)`, `kappa*kappa`, and `H*kappa^2`; the three
norm additions are doubling a*kappa, adding V, and adding 1. Projection
adds `rho*H` and `W+rho*H`. Thus the joint block is **5M+4A=9**, versus
5M+3A=8 before the substitution. The complete source is **77=41M+36A**,
30 positive coordinates and 19 equations. All expanded residuals pass.
This is the fully factored form, rather than reconstructing mu and hiding
its extra addition in the norm.

## 3. Sharing the main/input norm through the paid gap also costs 77

The paid c=kappa+phi suggests replacing the input norm by

    d_main^2-mu^2=D*phi*(c+kappa).

Using the already computed d_main^2, this takes `mu^2`, subtraction from
d_main^2, `c+kappa`, multiplication by phi, and multiplication by D:
**3M+2A=5**. The original input norm costs3M+1A=4. No kappa^2 is retained
in this variant. The exact polynomial identity is

    d_main^2-mu^2-D*phi*(c+kappa)
      = (d_main^2-D*c^2-1) - (mu^2-D*kappa^2-1)
        + D*(c-kappa-phi)*(c+kappa).

Consequently the retained main norm and gap give an exact positive-domain
witness equivalence, but the complete ledger again becomes77=41M+36A.
The extra c+kappa addition is not an already paid sum: the paid gap sum
is kappa+phi=c.

## 4. Evidence and scope

The checker builds four complete acyclic schedules, expands all76 source
comparisons across them (19 each), applies the actual auxiliary norm
correction, and verifies the histograms

    original:                76 = 41M + 35A
    translated root/marker:  76 = 41M + 35A
    factored projection:     77 = 41M + 36A
    shared norm difference:  77 = 41M + 36A.

It also checks192 exact positive input Pell/endpoint tuples and packing
identities. These are actual input bridge tuples, not materialized complete
universal compiler tableaux or astronomical auxiliary Pell coordinates.
The mathematical equivalences above apply to the full source; finite tests
are corroboration only. The counts rule out a saving for these precise
rewrites. They are not a lower bound for arbitrary arithmetic circuits,
other index congruences, or a redesigned universal input representation.
