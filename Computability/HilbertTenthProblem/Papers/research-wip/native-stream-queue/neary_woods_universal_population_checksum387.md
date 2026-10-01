# A padded checksum sign proof gives 387 universal operations

The [389-operation U9 polynomial](neary_woods_universal_population_projection389.md)
keeps the history checksum as a separate comparison because its value can
be negative on arbitrary positive assignments. Its fixed four-bit padding
nevertheless excludes the particular value -1 once the retained native
norms and outer comparisons hold. That conditional sign theorem permits
one additional factor in the final unit product and removes the separate
checksum comparison.

The result is **387=189M+198A polynomial operations**, **67 positive
existential witnesses**, **21 comparisons**, and four positive program
parameters besides ordinary positive input x. The certificate costs
**325=168M+157A**; total degree is **at most 2285**. The
[source](neary_woods_universal_population_checksum387.py) and
[receipt](neary_woods_universal_population_checksum387.json) contain the
complete DAG. This is an alternative explicit machine construction;
the separate best universal bounds remain75 certificate /87 polynomial.

## 1. The sign lemma before any AND interpretation

Use the history core's local names. Its unchanged positive fields and
padded ports satisfy

    F0,F1,F2,F3>0, q=16P^11>=16,
    F1+F3=16H+12, F2+F3=16M+10, F3=16Z+8.

Here P>=1 and F3>=8 hold on every positive supplied assignment of the
history wrapper: J=sum(Shat_i)-4>=0, P=(B-1)J+1>=1, and each decoded
hat packing is a polynomial with nonnegative coefficients in Shat_i-1,
ZUhat_i-1 and ZVhat_i-1. The old wrapper proves its joined Z>=0 without
using any AND equation or checksum. These same expressions are retained.
The native parameter q is unrelated to the recoder's same-named port.

Set

    C=q-(F0+F1+F2+F3),
    r=F0+qF1+q^2F2+q^3F3.

Assume C=-1 and the retained native equations. Then sum Fi=q+1, so
0<Fi<=q-2<q. Consequently

    q^3+q^2+q+1 <= r < q^4,
    r>q, r>=9.

The retained bound is X=r+positive_slack; also X=wq and Y=sq with
s=2*odd_half+1. These bounds provide every preliminary hypothesis of
[the binary selector proof, Sections2--4](native_controller_binary_selector56.md),
before its final one-hot partition step. Specifically E=XY>r+1,
a=Y(X+1)>2r+1, and the first Pell parameter exceeds the main one.
The retained first, main and full strong auxiliary norms, both positive
ratio slacks, index congruence and fixed-minus relations recover the
same main and first indices. The ratio and exponent proof then gives

    X=2^(2r+1),
    Y=binom(2r,r)+sum_(j=1)^r binom(2r,r+j)*X^j.

Since q divides X and r>q, q is a power 2^n, X is divisible by2q,
and odd Y/q implies n=v2(binom(2r,r))=popcount(r).
Thus

    q=2^n, n>=4, popcount(r)=n.                      (1)

No checksum equality C=1 or bitwise-AND theorem was used in this
recovery. The old selector proof used its checksum first to obtain
bounds; the assumed C=-1 supplies the same bounds here. The weaker
[raw population bootstrap](native_binary_input_dilation129.md),
Section2, also states exactly the r>=9,r>q hypotheses behind this step.

The padded ports give the low residues

    (F0,F1,F2,F3) = (3,4,2,8) modulo16.

Write Fi=16ai+di with ai>=0 and d=(3,4,2,8). Their low residues have
sum17 and total binary population5. Since sum Fi=2^n+1,

    sum ai=2^(n-4)-1.

There are no carries between the four base-q fields, since every Fi<q.
Binary population is subadditive under addition. Therefore

    popcount(r)=sum popcount(Fi)
               =5+sum popcount(ai)
              >=5+popcount(sum ai)
               =5+(n-4)=n+1,

contradicting (1). This includes n=4, when every ai is zero. Hence the
history checksum cannot equal -1 under the retained equations and the
native unit conditions. It is not claimed nonnegative on arbitrary
positive assignments.

## 2. Recovering both checksums without circularity

Let U be the parent's complete unit product. Its only factor without
an unconditional exclusion of -1 is the recoder checksum. All first,
main and auxiliary norm factors exclude -1 modulo4; in the normalized
form, so do the three normalized strong factors. The parent's proof
establishes these exclusions before native typing. Define the new unit
product U*C and remove the separate comparison C=1.

At a new polynomial zero,

    U*C*(1+sum of retained outer residual squares)=1.

Every product factor is an integer unit and every retained residual
vanishes. The unconditional norm sign arguments force all norm factors
to+1. Restore the old native root coordinates and, in the normalized
form, the complete old strong equations using the unchanged positive
coordinate maps. Those maps use the norm factors and positive supplied
coordinates, not either checksum. In particular all history core
hypotheses used in Section1 now hold, along with its two padded ports.
Section1 forces C=+1. The remaining recoder checksum is then+1 from
the unit product. Every parent equation has been restored.

Conversely every parent zero has U=C=1 and all retained residuals zero,
so is a new zero. Thus the old and new positive zero sets are identical
on the same coordinates. No witness replacement, new parameter or
relaxation of the ordinary-input semantics is involved. The U9 table,
positive program slice, exact least dyadic counter128n and independent
selected history remain unchanged. The established parent theorem gives,
for every recursively enumerable positive set S, fixed positive values
A_S,B_S,T_S,E_S such that

    x in S iff exists y_1,...,y_67>0:
    F(x,A_S,B_S,T_S,E_S,y_1,...,y_67)=0.

The new factor is justified by the padding-specific proof above; this
is not permission to multiply arbitrary independent checksums together.

## 3. Literal rewrite, correction and degree

The source checks the literal padded-port, field-sum and checksum rows,
the three supplied positive field coordinates, both port comparisons,
and the old factor list. It appends one multiplication U*C, removes
only the history checksum comparison, and changes the final product
comparison to the new register. All other certificate rows remain
identical. The polynomial saving is one extra product versus a residual
subtraction, square and sum: net **two additions/subtractions saved**.

Write S for the sum of squares of all retained outer residuals. The two
complete polynomials differ off zero:

    F_old=U*(1+S+(C-1)^2)-1,
    F_new=U*C*(1+S)-1,
    F_old-F_new=U*(C-1)*(C-2-S).

The verifier checks this correction, rather than claiming polynomial
identity at arbitrary supplied values. Both existing unit forms and all
four J/Ahat projection choices are supported, with either duration-bound
interface:16 ledgers in total. With both projections the native-unit
form costs390 operations,67 witnesses,24 comparisons,degree at most1449;
the normalized default costs387,67 witnesses,21 comparisons,degree at
most2285. The unmodified raw SOS source remains a separate alternative.

The inherited degree proof checks the three main-norm cancellations
on the actual source. The new history checksum has degree at most44;
multiplying it into the unit product adds at most44. The former residual
maximum remains a valid bound after deleting a comparison. Thus the
normalized bound is2241+44=2285 and the native-unit bound1405+44=1449.
These are conservative upper bounds, not exact degrees.

## 4. Evidence

Writer and fresh default replay verify512 complete polynomial corrections,
256 signed, across all16 configurations. Every old certificate register
is compared exactly; positive cases additionally verify P>=1,q>=16,F3>=8.
Fixed-numeral roles receive consistent finite values throughout the two
DAGs; their actual enormous values and all cross-role relations are not
materialized by those algebra tests.

The finite sign audit exhausts every composition of the high-part sum
for n=4,...,8. Each tuple has checksum -1 and the required low residues,
but its packed population is at least n+1. This illustrates the general
inequality proof; it is not a search for huge native Pell zeros.
Universality follows from the positive zero-set proof and the parent
theorem, not from these finite fixtures.

```sh
python3 neary_woods_universal_population_checksum387.py
```

Author writer, fresh default and full proof/source checks pass. Substrates'
independent final proof/source/fresh-default review passed without findings,
including 192 additional complete corrections (96 signed) across all16
configurations, 3,876 untyped field-composition bootstrap checks and288
population contradictions at widths4 through75. Native independently
confirmed the raw population theorem's checksum-free dependencies and
the low-residue contradiction. These reviews do not infer full native
zeros from the finite sign fixtures.
