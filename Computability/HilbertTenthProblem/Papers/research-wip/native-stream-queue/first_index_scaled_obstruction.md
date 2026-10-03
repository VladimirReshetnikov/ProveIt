# The asymmetric scale does not recover the deleted first-index congruence

There is an exact parametric obstruction in the **scaled first/main Pell subsystem**, including its strict ratio and main-root projection. It also admits three explicit instances satisfying the literal retained packing expression and the listed necessary mask conditions. Therefore those conditions alone cannot recover the missing first-index congruence after deleting h.

This is **not a full zero** of either81/82-operation candidate, not a valid compiled accepting history, and not a refutation or proof of the proposed universal projection. The input and auxiliary constraints remain outside the parametric construction. In particular it does not establish a new arithmetic upper bound. It closes the specific possibility left by [the previous scout](first_index_quotient_deletion_scout.md): the earlier p=27,n=15 example had odd Y and failed the mandatory asymmetric scale.

The [standalone checker](first_index_scaled_obstruction.py) and [receipt](first_index_scaled_obstruction.json) contain two small exact scaled Pell fixtures, four complete retained-candidate evaluations and the three larger packing instances. Nine frozen context files are authenticated. No predecessor Python or historical suite is executed.

## 1. Parametric scaled construction

Let t be any odd integer at least11. Define

    p=t(t+2), n=t(t+1), q=16,
    X=2^p, Y=2^(t+1),
    w=2^(p−4), s=2^(t−11),
    E=XY, a=Y(X+1), A=a+2, P=2XY²+1.

Then X=wq and Y=sq³ with w,s positive integers. Also p>n, p is3 modulo4, and

    p−n=t, 2n−p=t².

For the standard Pell sequences defined by

    chi_z(r)+psi_z(r)*sqrt(z²−1)
       =(z+sqrt(z²−1))^r,

put

    (D,c)=(chi_A(p),psi_A(p)),
    (tau,k)=(chi_P(n),2psi_P(n)).

The first and main positive norm equations are exact:

    tau²−XY²(XY²+1)k²=1,
    D²−(A²−1)c²=1.

The strict ratio kY<c<k(Y+1) is proved below. Hence

    eta=c−kY, zeta=k(Y+1)−c

are positive integers with eta+zeta=k. These are exactly the retained ratio-coordinate definitions, not alternative weak inequalities.

## 2. Elementary strict ratio proof

For every integer z≥2 and r≥1,

    (2z−1)^(r−1) ≤ psi_z(r) ≤ (2z)^(r−1).

This follows directly from psi_z(0)=0, psi_z(1)=1 and
psi_z(r+1)=2z*psi_z(r)−psi_z(r−1): the positive sequence is strictly increasing, so each ratio for r≥1 lies between2z−1 and2z. No deleted index relation enters this estimate.

Write B0=XY. The chosen powers have the exact balance

    (2B0)^(p−1)=2*(4B0Y)^(n−1)*Y.                (1)

Indeed their ratio is X^(p−n)/(2Y)^(2n−p), and

    X^t=(2Y)^(t²)=2^(t²(t+2)).

For the lower bound, 2A−1=2B0+2Y+3 and2P=4B0Y+2. Dividing the elementary bounds by(1) gives

    c/(kY) ≥
      (1+(2Y+3)/(2XY))^(p−1)
      / (1+1/(2XY²))^(n−1) > 1.                (2)

The strict inequality follows because p>n, both bases exceed1 and the numerator base is strictly larger.

For the upper bound, 2P−1=4B0Y+1>4B0Y, so

    c/(kY) ≤ (1+(1+2/Y)/X)^(p−1)
            ≤ (1+2/X)^(p−1).                   (3)

For an integer m≥1, u≥0 and m*u<1, the binomial expansion gives

    (1+u)^m ≤ 1/(1−mu),                         (4)

because each binomial coefficient is at most m raised to its index. Here

    2(p−1)(Y+1)<X.                              (5)

To verify(5) uniformly, t(t+2)≤2^t for every integer t≥6, by induction from t=6, since (t+1)(t+3)<2t(t+2). Therefore

    2(p−1)(Y+1)<4pY≤2^(2t+3)<2^(t²+2t)=X.

Equations(3)–(5) give c/(kY)<1+1/Y, proving c<k(Y+1). Together with(2) this proves the exact strict interval on every member of the family.

## 3. Main projection and failure of the inverse index

Let H=4a+3. The integer sequence

    e_r=chi_A(r)−a*psi_A(r)

has e_0=1,e_1=2 and the same second-order recurrence with coefficient2A. The sequence2^r satisfies that recurrence modulo H because5−4A=−H. Thus e_p=2^p=X modulo H, and

    gamma=(D−ac−X)/H

is an integer. It is greater than1. In fact D>(A−1)c=(a+1)c, hence D−ac>c. Since p≥3, c>A²; and A²−X>4a+3 because a²+1>X. Thus D−ac−X>H. Set rho=1 and sigma=gamma−1 to obtain two positive supplied coordinates and the exact retained main-root formula

    D=X+ac+(rho+sigma)H.

These large positive main indices also satisfy c>A(A²−1)² and c>2p. For example p≥6 already suffices for the first inequality by the explicit psi_A(6) polynomial. The obstruction is not caused by a small main rank.

If the target packed index is R=p, then P=1 modulo E and the same Pell recurrence gives psi_P(n)=n modulo E. Consequently

    k−R−1 = 2n−p−1 = t²−1 modulo E.             (6)

Here0<t²−1<E. The proposed inverse

    h=(k−R−1)/E

is positive rational but **not integral**. The numerator is positive since k≥2n>p+1. In particular2n=p+1 is false by the explicit difference t²−1. No index congruence or lower bound derived from the deleted equation has been used anywhere.

## 4. Literal packing and necessary mask instances

The following instances also satisfy the exact paid packing rows with

    B=16, J=1, MC=14, native MF0=4, paid MF=19,
    q=(B−1)J+1=16,
    G=q²−qF−Z,
    R=G(q²−1)+(MC+q*paidMF)J=255G+318.

| t | p=R | n | F | Z | G | Y exponent | Index remainder |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
|127|16383|16256|12|1|63|128|16128|
|177|31683|31506|8|5|123|178|31328|
|211|44943|44732|5|1|175|212|44520|

In every row F,Z are positive, F+Z<q, and

    (2q−1)(q²−1)<R<q⁴−q³.

The necessary mask conditions hold:0<MC,MF0<B−1, MC=2 modulo4, MF0=4 modulo8 and popcount(MC)+popcount(MF0)=4. They are **not** claimed to constitute an actual fixed-program compiler recipe. No control history, synchronized tape layout, complete input equation or auxiliary norm is supplied by this table. The full Pell integers in these three cases are defined by Sections1–3 and are not materialized by the checker.

The last row permits the additional arithmetic values x=1,alpha=1,twice_cell_bits=8, giving C=q−F−Z−alpha−8x=1 and W=C−Z=0. This is merely an extra outer arithmetic boundary; it is not a valid input-norm extension. The vanishing W must not be silently promoted to a full positive-source counterexample.

## 5. Exact finite evidence on both actual candidate arrays

The small independent exact fixtures are:

| p | n | X | Y | q | Index remainder |
| ---: | ---: | --- | --- | ---: | ---: |
|55|40|2^55|2^32|16|24|
|143|132|2^143|2^12|16|120|

The first was found by a bounded exact integer-root search; the second is t=11 from the parametric theorem. The receipt records every exact first/main value as hexadecimal integers. Independent binary Pell powering and repeated first-order recurrence agree. Both norms, all scale and ratio equations, the main projection, large-rank inequalities and the nonzero restoration remainders are checked exactly.

For each of the two saved full81/82 candidates, both small fixtures are embedded into a complete supplied positive integer assignment. Every one of the326 resulting paid row evaluations is executed, and all gates/ports are independently checked live. The actual first, main and transport factors equal1. These numerical embeddings deliberately use the last table's outer arithmetic F=5,Z=1,MC=14,paidMF=19, so their actual packed R is44943, **not their small main index p**. The receipt explicitly flags that mismatch. Their input and strong factors fail, and their full polynomial outputs are nonzero. They are implementation checks of the literal retained cones, not full-zero evidence.

The three large packing instances do have R=p and are covered by the exact parametric proof, but only their small parameter/exponent and outer arithmetic are evaluated. These two kinds of evidence are deliberately kept separate. No enormous auxiliary Pell extension is asserted or needed.

## 6. Consequence and remaining scope

The asymmetric scales, both positive Pell norms, the retained strict ratio, positive main projection and the displayed literal necessary-mask/packing arithmetic do not force integral restoration of h. A proof of the proposed deletion must use additional retained input, transport, strong or auxiliary information beyond this subsystem. This note does not establish that such a proof is impossible, and it does not exhibit a full positive zero violating the inverse.

Replay from any directory:

    python3 /absolute/path/first_index_scaled_obstruction.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/first_index_scaled_obstruction.json

All checks use explicit exceptions and exact integer arithmetic. No frozen parent files are changed. The writer and fresh normal and optimized saved-receipt replays from `/` passed.

Root independently read the complete proof and helper with no finding. Separate exact binary-power checks at t=11,13,15,17 confirmed both norms, the positive ratio gaps and integral gamma, large-rank margins and restoration remainder t²−1. These are supplemental independent checks; the author receipt remains two small fixtures and326 complete paid-row evaluations.
