# Two native index units: 301 operations on the same positive zero set

The complete [303-operation joint-AND polynomial](neary_woods_universal_joint_and_units.md)
can absorb both remaining native first-index comparisons into its unit
product. The resulting polynomial costs **301=144M+157A**, with the same
**51 positive existential coordinates**, four positive program parameters
and ordinary positive input. Its certificate costs **260=130M+130A** and
has **14 comparisons**. The conservative total-degree upper bound is
**2475**. The positive zero set is exactly the parent's, in the same
supplied coordinates; the polynomials differ away from their zeros.

The [literal source](neary_woods_universal_joint_and_arithmetic.py) and
[receipt](neary_woods_universal_joint_and_arithmetic.json) include either
single-core change and the unnormalized-strong unit parent as alternatives.
The separate best established75-certificate/87-polynomial route is unchanged.
No exact degree or optimality is claimed.

## 1. The exact source change and the sign question

For each native core use

    X=wq, Y=sq, E=XY, k=eta+zeta, c=kY+eta,
    a=Y(X+1), A=a+2, Delta=A²−1,
    R=2r+1, U=jc−R, Pfirst=2XY²+1.

Here q means Q in the geometry core and the padded joined scale in the
AND core. The supplied eta,zeta remain strictly positive, so

    kY<c<k(Y+1).                                      (1)

The parent first-index comparison is k=r+1+hE. Replace it by a unit
factor

    Nk=k−hE−r.                                       (2)

The old source contains r1=r+1 and R11=r1+hE. The r1 register remains
because the target R uses it. Change the single R11 addition to
R11=k−hE, then add Nk=R11−r and one multiplication into the existing
unit product. A literal consumer audit confirms that old R11 was used
only in the removed comparison. All other old registers retain their
values on arbitrary integer assignments.

Each changed core thus adds1M+1A to the certificate and removes one
comparison. The safe finalizer removes its residual subtraction, square
and sum addition, giving a net polynomial saving of one addition.
The proof below recovers Nk=+1; it does not assume its sign from the
product alone.

At a new zero, every retained outer residual is zero and every unit
factor is an integer unit. The six ordinary norm factors exclude−1
modulo4; each present normalized strong factor does too. Thus all norm
factors equal+1, while the sole joint checksum and the newly added index
factors are initially only±1. A core whose index comparison was retained
already has Nk=1.

For a normalized strong core, first set i_old=Delta*i. Its strong unit
restores the full old identity

    T²=Delta(f²−1), T=i_old*c²>0.                     (3)

The auxiliary coefficient becomes exactly T². In an unnormalized core,
(3) is still a retained comparison. The root-gap inverse restores the
original positive first Pell root in either case. Consequently both
cores have the same three native norms, full strong equation and
auxiliary congruence needed below, before checksum or bit typing.

## 2. Bounds before either index sign is known

Write r_g for the geometry index and r_j for the packed joint index.
These are different positive integers.

In the geometry core the literal source, for the actual fixed width
D>=3, gives

    q_input=x+input_slack>=2,
    Q=q_input+z+power_gap>=4,
    B=2^(D−1)Q>=4Q>=16,
    J=(B−1)*duration_quotient+ell>=B,
    r_g=(2^D−1)J>=7B>=112.

All coordinates displayed as slacks or quotients are positive; ell is
the positive paid program-duration expression. No dyadic or input-word
conclusion is used here. The retained bound is X>r_g. Also
s=2*odd_half+1>=3, so Y=sQ>=12. It follows directly that

    E>2r_g+1, a>2r_g+1,
    Y(r_g−1)>2(2r_g+1).                              (4)

In the joint core, the native scale is q=16L*Ph^11>=16. The four
fields Fi are positive before typing; in particular F3 is the old
positive padded low output plus a nonnegative high-history term.
The checksum is only known to be±1, so sum Fi is q−1 or q+1.
The literal packing therefore gives

    r_j=F0+qF1+q²F2+q³F3,
    4369<=q³+q²+q+1<=r_j
         <=(q−2)q³+q²+q+1<q⁴.                       (5)

For the upper bound, put one unit in each of the three lower fields
and all remaining mass in the highest field, allowing the larger sum
q+1. Each Fi<q follows from positivity of the other three fields;
there is no bitwise assumption. The retained bound X>r_j and Y>=q>=16
imply all three inequalities (4) with r_j in place of r_g.

Hence, in either core, r>=112, Y>=12, X>r, E>2r+1 and
Y(r−1)>2(2r+1). Also Pfirst>A. These are enough for the local sign
argument; geometry does not need a field checksum or an upper r<q⁴.

## 3. Recovering each index before applying the parent theorem

This is the [native index-unit proof](group_projective_index_unit.md),
with its strict bounds established separately in Section2. Here are
its hypotheses and deduction in the present two-core setting.

The restored positive first norm gives k=psi_Pfirst(n), n>=1. Since
Pfirst=1 mod E, the Pell recurrence gives k=n mod E. If Nk=epsilon
with epsilon in {−1,1}, equation(2) implies

    n=r+epsilon mod E, and hence n>=r−1,              (6)

because 0<r−1<r+1<E. The main norm gives c=psi_A(p), p>=1. Monotonicity,
Pfirst>A and c>k imply p>n, so p>=r>=112. Elementary Pell growth yields

    c>A*Delta², c>2p,
    c>Yk>=Y(r−1)>2(2r+1).                            (7)

For example psi_A(p)>(2A−1)^(p−1)>A^6>A*Delta² at these parameters.
The retained auxiliary linear comparison is U=of−c. Since also
U=jc−(2r+1) and j>=1, (7) gives U>0.

The integral-rank argument in the
[relaxed auxiliary proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md)
uses A>1, c=psi_A(p)>A*Delta² and exactly the strong equation(3),
with c² dividing T. It gives an auxiliary index m such that
f=chi_A(m), c divides m and m>=c>2p. It does not need checksum=1,
a dyadic conclusion or a recovered first index.

The auxiliary norm is (TU)²−(T²−1)y²=1. Its positive solution has an
odd index ell_aux=2v+1. The odd-index identities and signed step-down
argument in the
[half-parameter proof](../../1980/HALF_PARAMETER_PELL_92_PROOF.md)
use U=−c mod f, U=−(2r+1) mod c and0<2p<m. They give

    2r+1=±p mod c.

The strict inequalities0<p,2r+1<c/2 in (7) force

    p=2r+1.                                         (8)

This is the generic rank and signed congruence proof, not an invocation
of the complete typed native theorem. Combining n<p=2r+1<E with (6)
now gives n=r+epsilon exactly.

If epsilon=−1, then p=2n+3. Put A2=2A²−1. Direct substitution gives
A2>Pfirst and2A>Y+1. The Pell duplication identity then gives

    c=psi_A(2n+3)>psi_A(2n)
      =2A*psi_A2(n)>=2A*psi_Pfirst(n)>k(Y+1),

contradicting the upper ratio in (1). Thus Nk=1 in this core.

The argument applies to each changed core independently. It does not
require the other index sign or checksum sign to have been restored.
Once all changed indices are+1, their product and the norm signs force
the single checksum to+1. Every comparison and unit of the complete
parent is now restored. Conversely every parent positive zero has
Nk=1 for both cores, so satisfies the new polynomial. The supplied
positive coordinates are identical and no new canonical auxiliary
choice is needed for this additional rewrite.

The same local proof applies if a finalizer groups the factors in a
different way, provided its zeros force every listed factor to±1 and
all retained outer residuals to zero. The proof uses those facts, not
the particular multiplication order of the single unit product.

## 4. Literal output correction and degree bounds

Let U be the old unit product, R_i the removed first-index residuals,
and S the sum of the squares of all remaining outer residuals. The
old and new outputs are exactly

    F_old=U*(1+S+sum R_i²)−1,
    F_new=U*product(1+R_i)*(1+S)−1.

The checker verifies every unchanged source register, each new factor,
all retained residuals and the complete correction

    F_new−F_old
       =U*((product(1+R_i)−1)*(1+S)−sum R_i²).         (9)

This is not an equality of the two off-zero polynomials.

The degree audit runs over the actual source and uses only the parent's
guarded main-norm cancellation. The new geometry factor has degree at
most5 and the new joint factor at most185. The maximum outer residual
bound stays206 in the ordinary-unit form and185 in the normalized
form. The following bounds include all program coordinates.

| Strong treatment | Index factors added | Certificate | Comparisons | Polynomial | Degree upper bound |
|---|---|---:|---:|---:|---:|
| Ordinary units | geometry |254|17|304=142M+162A|1480|
| Ordinary units | joint |254|17|304=142M+162A|1660|
| Ordinary units | both |256|16|303=142M+161A|1665|
| Both normalized | geometry |258|15|302=144M+158A|2290|
| Both normalized | joint |258|15|302=144M+158A|2470|
| Both normalized | both |260|14|**301=144M+157A**|**2475**|

Every row has51 positive witnesses. Both the four-program interface
using program_E as duration bound and the independent fifth-bound
interface have these same counts and degree bounds. The universal
ordinary-input relation follows from the exact same-positive-zero-set
proof and the parent's already complete U9 construction.

## 5. Verification and scope

The writer audits12 source ledgers and768 complete parent/new output
corrections,384 signed. Fixed numeral roles receive consistent finite
substitutions; positive fixtures use radix4 and divisor7. These cases
check literal source identities, not full positive Pell zero tuples.
The receipt also includes192 geometry bootstrap fixtures,1568 weak
joint-checksum fixtures and1152 exact Pell duplication cases. The last
two reuse the independently proved index packet's finite audit functions.
Five malformed-source variants verify the critical-row and private
consumer checks.

```sh
python3 neary_woods_universal_joint_and_arithmetic.py
```

Final review passed. The author writer and fresh default replay passed;
root reviewed the complete proof and source and ran a fresh default
replay. Every301-source gate reaches the final output. An independent
reviewer checked the full proof, source and fresh replay without findings,
then added288 independently executed complete output corrections,144
signed, across all12 options. Its positive numeral roles included widths
3,4,7. These algebraic checks supplement the sign and positive zero-set
proofs; none claims to materialize giant Pell witnesses.
