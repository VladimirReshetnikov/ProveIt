# Independent ordinary review: canonical-sign square extraction over naturals

**Decision: PASS in the stated ordinary-mathematics and finite-artifact scope.**
Reviewed 25 October 2026. This is a separate AI-assisted mathematical/artifact review,
not external human peer review, an upstream acceptance decision, or an end-to-end
proof-assistant certificate.

The new raw source has310 nonnegative coordinates and262 quadratic residuals.
The exact selected contractions inspected here are:

| Domain | Variables | Rows | Exact degree | Collected terms | Height |
|---|---:|---:|---:|---:|---:|
| Nonnegative integers |206|158|4|9167|560710452|
| Nonnegative integers |208|160|4|6183|83847165|

Every coordinate remains independently nonnegative. The result is a natural-domain
tradeoff and must not be presented as a240-integer-variable replacement or a global
minimum. Both endpoints' full SOS expansions and every domain-preserving monic
restoration were independently recomputed without importing or running author code.
Later residual-basis improvements require their own exact identities and metrics.

## 1. Literal source identity

The unchanged old local value is

    R = (product_(i=0..8) delta_i^2)
        (delta11^2+delta12^2) delta13^2 delta14^2,

where delta0=S−Sp, delta_i=S−Sp−m_i for1≤i≤8,
E=(a−c)(b−c), D=d+2, delta11=E²−D²,
delta12=S−Sp−mul.358, delta13=mul.363−mul.369,
and delta14=mul.372−mul.373.

The emitted new gates compute

    Q = (product_(i=0..8)(−delta_i)) (−delta13) delta14,
    Z0=Q(E−D),  Z=Z0(E+D),  T=Q(−delta12).

Thus Z²+T²=R identically, without sign hypotheses. This is not a replacement of
R by its square root: the final evaluation row retains BOTH Z² and T² and the
two original beta-difference squares. In particular it retains the congruence to
N times the original evaluation quotient. Dropping that row would invalidate the
construction; the independent checker rejects that exact corruption.

At the actual row level28 square/product definitions are removed and14 oriented
product definitions added. All247 other old rows are unchanged by exact name-level
coefficient comparison. Neither the old semantic atom list nor the label polynomial,
Pell frame, powers, ranges, endpoints, or local-source majorant changes.

## 2. Soundness and domain preservation

From any natural zero of the new raw source, restore all deleted sqd.i as their
literal squared differences, then mul.355, mul.357 and the old multiplication chain.
These are natural values regardless of the signs of the underlying differences.
The exact identity above restores the old complete evaluation row. Hence every
new natural zero yields an old natural zero, and the retained old arithmetic and
C222/ZF/ZFC calibration applies in its existing order.

This soundness argument does not pretend that an arbitrary old natural tuple has
nonnegative new partial products. The reverse direction is only canonical
completeness, not a full bijection of the two raw auxiliary zero sets. That is
sufficient for equivalence to existence of a finite refutation.

## 3. Canonical CRT lifts: no circular source choices

The proof chooses, in order:

1. finite proof tree, even t≥4, F=t!, n=F²−1, V=n^t, y=V−1;
2. beta-CRT witness x, enlarged within its class; B=binom(n,t), N=B^x;
3. positive precision-N² classes for all encoded columns;
4. c,d,S,u,v,index; then b>c; then Sp>S;
5. a in its fixed class, beyond c+d+3 and every previously fixed seed index,
   with (S+1)(1+F(a+1))>(Sp+1)(1+F(b+1));
6. self-sized sum S_base, q=(N*S_base)^x, denominators and frame W;
7. large common-root-compatible Pell base and fresh private witnesses.

All conditions in step5 are lower bounds on a. Since N is already fixed, a full
tail of its arithmetic progression meets them. No representative is chosen using
its own later q or Pell base, and no condition asks S or Sp to exceed the later
syntax-label sum. This is a valid well-founded choice order.

Adding any multiple of N² preserves every inherited precision-2x congruence.
Range-binomial divisibility is not inferred from a false converse of the range
lemma: the precision-N² construction and the factorial denominator-loss argument
remain the retained completeness proof. The local high-degree polynomial is
unchanged, so all local polynomial congruences and bounded-row majorants transfer.

The old self-radix proof explicitly removed an upper bound on representatives.
The current q depends on their actual post-lift sum. Thus the earlier convenient
[1,N²] or[1,2N²] choices are not binding constraints on this construction.

## 4. Every new factor and partial product is nonnegative

The following facts follow from actual raw parent rows, not from variable names:

- g0=Sp−S>0, and g1,…,g8 are g0 plus existing natural product gates.
  The separate factor Sp−S+mul.358 is positive.
- mul.361=F(b+1), mul.363=(Sp+1)(1+F(b+1)),
  mul.364=F(a+1), mul.368=(S+1)(1+F(a+1)),
  mul.366=F(4+4b+2mul.36),
  mul.369=(1+mul.366)mul.368.
  The chosen a makes mul.368>mul.363, hence g9=mul.369−mul.363>0.
- mul.370=F(6+4b+2mul.36),
  mul.372=(Sp+1)(1+mul.370),
  mul.373=(S+1)(1+mul.361).
  In particular mul.370−mul.361=F(5+3b+2mul.36)>0. Together with Sp>S,
  this gives g10=mul.372−mul.373>0.
- b−c≥1 and a−c>d+3 imply E>D=d+2>0. Thus E−D,E+D are positive.

All ten successive Q product gates and E,Z0,Z,T are therefore natural. The
new local value remains the same nonnegative multiple of N, so the unchanged
evaluation quotient is natural too. This covers all14 newly introduced gates.

## 5. Anchor dominance and later remainder budgets

The actual raw merged-bound row has semantic anchor

    J = 7 + 4b + 2mul.36 + add.402,
    mul.36 = (a+b)^2 + 5(a+b) + 6.

All the other terms are nonnegative. Hence

    J≥7+2[(a+b)^2+5(a+b)+6] > 2(a+1)^2.

With a chosen after the other fixed seed indices, J≥2max_i k_i follows,
including its own a+1 seed. This is the precise sufficient hypothesis of the
retained one-row semantic-anchor completeness theorem. That theorem states
explicitly that it needs **neither parity of J nor a doubled frame**. No new
parity condition is needed for this natural-domain construction.

After the lifts each representative is still less than S_base, and the literal
constructor bound J≤S_base^(2^22) is unrestricted in representative size. The
already fixed inequality2^22(t+1)<x therefore still controls derived-label
binomial coefficients. Ordinary coefficients are≤S_base^x and factorial
coefficients≤V<N. The pooled-budget estimate

    5 S_base^x + N < N^x S_base^x = q

is unchanged. It supplies the four pooled natural slacks even after unbounded
representative lifts. The common-root and private Pell choices occur only after
these quantities, so no hidden feedback is introduced.

## 6. Exact contractions and independent finite checks

`check_natural_independent.py` in this directory imports only Python standard
library modules, reads JSON, and imports no producer, author checker or inherited
module. It verifies:

- copied parent raw file is byte-identical to the incoming Cofinal package;
- all removed/new literal gate equations and both formal polynomial identities;
- all247 otherwise unchanged source rows and retained source-evaluation row;
- each of104 (dimension) and102 (sparse) monic eliminations;
- every rational positive-weight affine-square/nonnegative-monomial certificate;
- every target row, row order, coordinate identity, degree bound and liveness;
- every coefficient of both complete SOS expansions;
- seven deliberate corruption controls, rejected at the intended checks.

The only negative-coefficient restorations in either contraction are the two
unchanged beta squares sqd.15 and sqd.16. Their certificates are literal squares
of affine integral forms; no unsupported sign-restricted monic substitution is
used. All other eliminated restorations are coefficientwise nonnegative.
Normal and optimized Python runs succeed with byte-identical JSON receipts.

## 7. Exact bindings and scope

Inspected PROOF.md SHA-256: `73b5f6afdef9f1901a1d1078df827d1f12f7ad4c90d5b459bd969b27d0730434`.
Parent raw file SHA-256: `c0bad9e9b861410b9dad70ff6bb2138e52448dcd27f13e665bf749389d7d7e61`.
New raw file SHA-256: `3f9eec27daa9597786b108f7da94e52b40495a54afdfd4be3ac8175b40559b57`.

- `natural/trial_corrected/inherited24`
  - equation: `c73a3564ce4be179cd3c77c73a438ff16317e1097041abdcd5ca4d5fcec5f1c2`
  - expansion: `773d2c662d7ca058b9ba8846f53e3deb157e4e512fe410659459ea30526d9dfe`
  - elimination certificate: `c2bace17077dcf8d87f8258b4faded21d60f9100684208dcb0e38d518fc77d03`
- `natural/trial_corrected/default32`
  - equation: `16cff1cccd39b5abfe80e1b8529b839da16f0b70ec9a77781bc090f5ec305299`
  - expansion: `284f0ee24982cb423e60893f7f52da8217082ae946137d5df0d554e88af2298d`
  - elimination certificate: `41a3c2158c5917abda55f8f3dac470422118e7078e3dbad13668a54110ad33f1`

The complete receipt is `NATURAL_INDEPENDENT.json`; the normal-mode duplicate
is `NATURAL_INDEPENDENT_NORMAL.json`. The two process logs and checker source
are retained. These finite checks do not search for a refutation, decide Con(ZFC),
rebuild the inherited transitive proof-assistant environment, or establish global
optimality. The ordinary review accepts the new semantic delta relative to the
explicitly retained prior arithmetic/logical proof contracts.

No unresolved mathematical blocker was found within that scope.
