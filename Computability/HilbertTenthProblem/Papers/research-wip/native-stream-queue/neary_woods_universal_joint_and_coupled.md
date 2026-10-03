# Coupled native linear units: a complete 297-operation U9 polynomial

The [301-operation two-index compiler](neary_woods_universal_joint_and_arithmetic.md)
has a **297=144M+153A** successor, with **51 positive existential
coordinates**, four positive program parameters and ordinary positive
input. Its certificate costs **262=132M+130A**, with **12 comparisons**.
Its conservative total-degree upper bound is **2311**, including program
coordinates. The [source](neary_woods_universal_joint_and_coupled.py) and
[receipt](neary_woods_universal_joint_and_coupled.json) contain the entire
literal certificate and polynomial DAG.

The two coupled auxiliary comparisons save two polynomial additions
each. Soundness needs more than the earlier one-core transplant: the
geometry index is computed from the outer recoder and cannot be shifted
freely. A population contradiction in the joint core excludes its
negative index branch. The remaining negative joint branch normalizes
by changing just two private positive coordinates. Thus the accepted
outer relation is unchanged, but the new and parent positive zero sets
are not asserted identical in their supplied witness coordinates.

The fixed U9 program, all fixed-numeral recipes, paid ordinary-input
bridge and chronological tag history remain those of the complete parent.
No new universal-machine promise or input recoding is introduced. The
separate75-certificate/87-polynomial route remains unchanged.

## 1. Literal coupled factors

For each of the two cores use the parent's notation

    X=wq, Y=sq, E=XY, k=eta+zeta, c=kY+eta,
    a=Y(X+1), A=a+2, Delta=A²−1,
    K=k−hE, Nk=K−r, V=of−c, U=jc−(2r+1).

Here q=Q in the geometry core and q is the joined padded native scale
in the joint core. The actual source already computes K as R11.
Both positive ratio slacks are retained:

    kY<c<k(Y+1).                                      (1)

Replace U by V in the auxiliary square and introduce

    Nl=V−jc+2K.                                      (2)

Multiply Nl into the unit product and delete the comparison U=V.
The auxiliary unit is now

    N3=W*(V²−y²)+y².                                 (3)

For an ordinary-strong core W=Delta*(f²−1), with the full strong
comparison retained. For a normalized core W=Delta²*(ic²)², together
with the strong unit Ns=f²−Delta*(ic²)². In the latter case Ns=1
restores the full strong equation with i_old=Delta*i. In both cases
we may use the positive native parameter T=i_old*c² and W=T² after
restoring that strong equation.

The three deleted gates per changed core are

    r1=r+1, tr1=r1+r, U=jc−tr1.

Replace them by the three additions/subtractions

    twice_K=K+K, difference=V−jc, Nl=difference+twice_K.

The existing square now computes V². One added product multiplication
and one removed comparison give the exact two-operation polynomial
saving. The source audits all consumers of the deleted registers.
It also checks that the later negative-branch coordinates F0 and the
joint X-bound slack have only their expected private consumers.

## 2. Recovering both linear signs before typing

At a new positive zero the safe integer-product finalizer makes every
retained outer residual zero and every unit factor±1. All first, main,
auxiliary and present normalized-strong norms exclude−1 modulo4.
Consequently the norms are+1. The index factors, linear factors and
joint checksum remain signed at this stage.

Write epsilon_g,epsilon_j for the two index signs and lambda_g,lambda_j
for the new linear signs. Temporarily allowing all of them to be±1,
the checksum is

    C=q_joint−sum Fi=epsilon_g*epsilon_j*lambda_g*lambda_j. (4)

The source positivity and retained bounds are exactly those established
in the two-index parent. The geometry core has

    Q>=4, B>=4Q>=16, J>=B, r_g=(2^D−1)J>=7B>=112,
    X>r_g, Y>=12,

for the actual fixed width D>=3. The joint core has q>=16, all Fi>0,
sum Fi=q±1, X>r_j and

    q³+q²+q+1<=r_j<q⁴, r_j>=4369, Y>=16.             (5)

These facts precede native typing. In either core they imply the
slightly stronger inequalities

    E>2r+3, Y(r−1)>2(2r+3).                          (6)

Let Jnew=2K−lambda, where K=r+epsilon. Then
2r−3<=Jnew<=2r+3. The restored first norm gives
k=psi_Pfirst(n), Pfirst=2XY²+1, with n=K mod E and n>=r−1.
The main norm and (1) give c=psi_A(p), p>n and p>=r. Thus the same
Pell growth estimates as in the parent give

    c>A*Delta², c>2p, c>Y(r−1)>2Jnew.                (7)

The full strong rank theorem gives f=chi_A(m), c divides m and
m>=c>2p. In particular
f>chi_A(2p)=1+2Delta*c²>2c, so V=of−c>0 before classifying the
auxiliary Pell solution. This is essential because V is a signed
arithmetic expression before these equations are used.

Now N3=1 is (TV)²−(T²−1)y²=1. The unchanged congruence
V=−c mod f, and (2) giving V=jc−Jnew, yield exactly the odd-index and
signed step-down argument of the
[coupled linear-unit proof, Sections2–3](group_projective_coupled_linear_unit.md).
Its hypotheses are the full strong equation and (7), not a typed
checksum. It gives p=Jnew. Since0<n<p<=2r+3<E, the congruence above
identifies n=K exactly.

If lambda=−1, then p=2n+1. The strict inequalities
2A²−1>Pfirst and2A>Y+1, together with Pell duplication, imply

    c=psi_A(2n+1)>psi_A(2n)
      =2A*psi_(2A²−1)(n)>=2A*k>k(Y+1),

contradicting (1). Therefore each new linear sign is+1. We now know

    p=2K−1, n=K, C=epsilon_g*epsilon_j.              (8)

If only one core is coupled, the untouched core's existing index sign
proof restores its epsilon=1 independently of the signed checksum.
All arguments below still apply with that sign fixed to+1.

## 3. The raw population theorem at the shifted native index

For either coupled core define

    r'=K−1=r+epsilon−1,                              (9)

which is r or r−2. Equation(8) says its main Pell index is2r'+1;
its first index equation is k=r'+1+hE. Also Nl=1 gives
V=jc−(2r'+1). Thus every raw scalar native equation is restored at
r', with the old first-root inverse and full strong equation already
available. The exponent comparison, both ratio slacks and odd multiplier
s=2*odd_half+1 remain unchanged. X>r' is restored by adding
1−epsilon to the positive X-bound slack.

The necessary raw-kernel bounds hold without field typing. Geometry
has r'_g>=7B−2>B>Q and r'_g>=110. The joint core has
r'_j>=q³+q²+q−1>q and r'_j>=4367. Consequently the
[raw geometry theorem at index>=9 and index>scale](native_binary_input_dilation129.md#2-the-raw-geometry-theorem-at-j9-and-jq)
applies separately to these scalar native values. If its auxiliary
index-bound comparison is written explicitly, choose its bound to be
the positive scale and its slack to be r' minus that scale. These are
known positive values used to invoke the theorem, not extra supplied
coordinates in the new circuit.

The theorem gives, before any truth-field decoding,

    Q=2^popcount(r'_g),
    q_joint=2^popcount(r'_j).                         (10)

For an untouched core the same statement holds at r'=r after its
index sign has been restored. The theorem does not require the new
r' to equal the original packed or recoder-computed r. No altered outer
recoder equation has been assumed: (10) is solely a consequence of
the fully restored raw native equations at the numerical index (9).

## 4. The joint population excludes a negative geometry sign

Let q=q_joint=2^t. It is a multiple of16, so t>=4. The exact retained
ports and padding give

    F3=8, F1=4, F2=2 mod16,
    F0=2−C mod16.                                   (11)

The weak checksum and positivity imply0<Fi<q. Therefore the four
base-q fields in r_j are disjoint binary blocks, and

    popcount(r_j)=sum_i popcount(Fi).                (12)

Suppose epsilon_g=−1. By(8), C=−epsilon_j. There are two cases.

* If epsilon_j=+1, then C=−1, sum Fi=q+1 and the low residues are
  (3,4,2,8). Write Fi=16ai+di with these residues; ai>=0 and
  sum ai=2^(t−4)−1. The low residues have total population5, hence
  popcount(r_j)>=5+popcount(sum ai)=t+1. But r'_j=r_j and(10)
  requires popcount(r_j)=t, a contradiction.
* If epsilon_j=−1, then C=+1 and sum Fi=q−1. Equation(12) gives
  popcount(r_j)>=popcount(q−1)=t. Also r_j=1 mod16. For every r>1
  with r=1 mod16,

      popcount(r−2)=popcount(r)+v2(r−1)−2
                  >=popcount(r)+2.                  (13)

  Indeed, write r−1=2^v*u with u odd and v>=4, then subtract2
  explicitly. Now r'_j=r_j−2 has population at least t+2, again
  contradicting(10).

Both cases are impossible, so

    epsilon_g=1, C=epsilon_j.                       (14)

This is the extra step needed for the computed geometry index. It does
not shift J, Q, the input, duration, any history field or any program
parameter. In particular, the geometry negative branch has not been
silently identified with a different recoder instance.

## 5. Positive restoration of the remaining joint branch

If epsilon_j=+1, all new linear and index units are+1 and every old
comparison is restored in the same supplied coordinates.

If epsilon_j=−1, equations(11) and(14) imply F0=3 mod16 and therefore
F0>=3. Define only

    F0_old=F0−2>0,
    bound_beta_old=bound_beta+2>0                    (15)

in the joint core. Its computed packed r becomes r_old=r_j−2.
The checksum becomes+1, while K=r_j−1=r_old+1 and

    jc−(2r_old+1)=jc−(2K−1)=V.

Thus the old auxiliary norm equals the new one. The first index,
X bound, both input ports, main norm, first norm and strong factor or
comparison are all restored. All geometry and outer source registers
retain their values; this is audited against the complete DAG.

The resulting tuple is a positive zero of the301 parent (or its
ordinary-strong variant). Conversely every parent positive zero has
Nk=1 and U=V in each core, so Nl=1 and every new factor/comparison
holds with the same supplied coordinates. This proves the same
accepted relation on every outer coordinate. In particular, the fixed
ordinary-input universal relation is preserved with51 witnesses and
the same four program parameters.

If the geometry core alone is coupled, both index signs are forced+1
and the positive zero set is identical. When the joint core is coupled,
(15) is a conditional normalization; no positive-tuple bijection is
claimed.

Unlike the earlier index-only packet, not every factor is+1 at every
new zero: the joint checksum and index can both be−1. For a future
partitioned finalizer, any grouped zero that forces every group product
to1 is sound by the present all-product theorem. Completeness still
holds because every parent301 zero enters with every factor+1.
Such grouping preserves the accepted outer relation, but need not
preserve the coupled packet's exact positive zero set.

## 6. Source identities and degree upper bounds

On arbitrary supplied integer assignments, let r_lin=U−V be the
removed parent residual and let W be its literal auxiliary coefficient.
Then the changed factors satisfy exactly

    N3_new=N3_old+W*(V²−U²),
    Nl=2Nk−1−r_lin.                                 (16)

All other retained residuals are identical. The verifier forms every
new factor and the complete finalizer from these corrected parent
values; it never divides by a potentially zero factor. The polynomials
are not asserted equal away from their common accepted projection.
On the conditional locus epsilon_g=1, C=epsilon_j and every Nl=1,
restoration(15) makes the entire parent residual/output schedule agree,
even if the norm equations themselves are off zero.

The source substitutes V into the actual auxiliary square. It does
not use an equation to lower the polynomial degree. In the normalized
form the auxiliary factor bounds change from38 to36 in geometry and
from976 to708 in the joint core. The new linear factors have bounds5
and101, respectively. All other factor bounds are inherited. With
both couplings the product bound is1941 and the maximum outer residual
bound remains185, giving1941+2*185=2311. In the ordinary-strong form
the auxiliary bounds become16 and304 and the largest residual remains206.

| Strong treatment | Coupled cores | Certificate | Comparisons | Polynomial | Degree upper bound |
|---|---|---:|---:|---:|---:|
| Ordinary units | geometry |257|15|301=142M+159A|1668|
| Ordinary units | joint |257|15|301=142M+159A|1498|
| Ordinary units | both |258|14|299=142M+157A|1501|
| Both normalized | geometry |261|13|299=144M+155A|2478|
| Both normalized | joint |261|13|299=144M+155A|2308|
| Both normalized | both |262|12|**297=144M+153A**|**2311**|

All rows have51 positive witnesses. Both four-program and independent
fifth-duration-bound interfaces have these counts and bounds. Degrees
include all program coordinates and use only the inherited guarded
main-norm cancellation. No exact degree or global optimality is claimed.

## 7. Checks and evidence limits

The writer covers12 complete ledgers and768 full factor/output
corrections,384 signed. Another240 structured conditional restorations
cover180 positive and60 signed assignments, including96 negative-joint
cases. They enforce both input ports and the relevant sign relations,
then check every retained residual, every outer register and the entire
restored-parent output. They are off-zero norm fixtures, not numerical
claims to have expanded full positive Pell solutions.

The receipt also contains1,249 exact carry identities(13),320
negative-checksum population fixtures and56 strengthened target-bound
checks. The proofs, rather than these finite samples, establish the
sign recovery and the raw native theorem's applicability at r−2.

```sh
python3 neary_woods_universal_joint_and_coupled.py
```

The author writer and a fresh default replay passed. An independent
reviewer completed the full proof/source review and another fresh replay
with no findings. That review checked both local sign arguments, the raw
population theorem at the shifted indices, the positive F0−2/beta+2
restoration, both interfaces and every count/degree alternative. A
separate literal executor also passed192 complete scalar-factor/output
identities across all12 options,96 signed. All five local links resolve.
The root reviewer independently read the full proof and source and ran
a fresh default replay; all passed with no findings.
