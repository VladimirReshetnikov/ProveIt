# Positive scale coordinates give a291-operation universal U9 polynomial

The [coupled297 construction](neary_woods_universal_joint_and_coupled.md)
has a **291=142M+149A** successor with **49 positive existential
coordinates**, ten comparisons and the same four positive program
parameters and ordinary input. Its certificate still costs
**262=132M+130A** operations. The literal polynomial has total degree
**at most3980**; the lower operation count increases this degree bound.

The change absorbs each native size comparison into a stronger positive
parametrization of its scale. Its inverse is positive at every parent
zero by the parent's exponential/population theorem, including the
negative joint-index branch. Thus it gives an explicit bijection between
the positive zero sets after the stated coordinate change. The programs,
recoder, history and accepted ordinary inputs remain unchanged. The
separate established75-certificate/87-polynomial bounds are unchanged.

The [source](neary_woods_universal_positive_scale291.py) and
[receipt](neary_woods_universal_positive_scale291.json) retain both
program-duration interfaces and single-core variants.

## 1. The coordinate change and literal source

For either native core write q for its positive scale and r for its
computed packed index. In geometry these are Q and geometry_index;
in the joint core they are and__q and and__bs_packed. The old circuit
supplies positive w,beta and computes

    X=q*w, bound=r+beta, with comparison bound=X.       (1)

The w coordinate occurs only in the multiplication defining X. The
beta coordinate occurs only in bound. That bound register occurs only
in its comparison. Neither q nor r depends on any of the coordinates
being changed in either core; the source audits this transitive
dependency statement, not just the immediate consumers.

Keep one positive supplied coordinate b in place of beta, omit w, and
compute instead

    bound=r+b, X=q*bound.                              (2)

Delete the comparison in(1). Both gates in(1) are reused in(2): no
gate is added or erased. A topological sort places bound before X.
The literal coordinate retains the old spelling bound_beta, but its
meaning is now the positive gap w_old-r. There is no division operation
in the new circuit.

All four positive ratio slacks and both complete strong equations are
retained. No native index, norm, checksum, input port or controller
equation is omitted by this rewrite.

## 2. Soundness and exact off-zero identity

The inherited outer source gives q>=4 and r>0 for geometry, and q>=16
and r>0 for the joint core, before applying any native typing theorem.
For geometry use B>=16 and

    J=(B-1)*duration_quotient+program_duration_bound>0,
    r=(2^D-1)J>0.

For the joint core the four supplied/computed truth fields are strictly
positive and r is their positive base-q expression. These facts do not
use either omitted comparison.

Given a new positive tuple, restore the old coordinates by

    w_old=r+b,
    beta_old=q*(r+b)-r=(q-1)r+q*b.                    (3)

Both are strictly positive. The old X equals the new X, and the old
bound becomes exactly X. Every old comparison is restored. All other
source registers agree except for the intentionally repurposed bound
register. In particular every unit factor and every remaining residual
agrees, so the old product theorem proves soundness.

This is also an exact polynomial identity on arbitrary integer supplied
coordinates, with no domain or zero assumption: if Phi is(3), then

    P_new(values)=P_parent(Phi(values)).               (4)

The removed comparison residuals vanish identically under Phi. Both
transformations may be applied simultaneously because q and r in
either core are independent of all changed coordinates. Positivity is
needed for the Diophantine domain, not for the algebraic identity(4).

## 3. Positive inverse at every old zero

At any positive zero of the coupled parent, its raw native theorem gives

    r'=r+epsilon-1, X=2^(2r'+1), q=2^popcount(r').      (5)

In geometry epsilon=1 and r'>=112. In the joint core epsilon may be
either sign, and r'>=4367. These are conclusions of the reviewed
[coupled sign and shifted-index proof](neary_woods_universal_joint_and_coupled.md#3-the-raw-population-theorem-at-the-shifted-native-index)
and its complete raw native theorem, not assumptions about supplied
truth-field typing. In particular (5) remains valid when the joint
index and checksum are both negative.

Since popcount(r')<=r', we have

    w_old=X/q=2^(2r'+1-popcount(r'))
         >=2^(r'+1)>r'+2>=r.                         (6)

The strict elementary inequality holds for every r'>=2, far below the
actual lower bounds. Therefore define

    b=w_old-r>0.                                    (7)

This gives the new X=q*(r+b)=q*w_old. Every other native, recoder and
history quantity is unchanged, and the new polynomial vanishes.
Equations(3) and(7) are inverse maps: the old comparison recovers
beta_old=q*w_old-r, while q and r do not change. This proves the claimed
positive witness bijection with the two w coordinates omitted and the
two beta coordinates reinterpreted. It proves more than completeness
only from specially chosen canonical parent witnesses.

The fixed U9 table, exact fixed-numeral recipes, effective program slices
and paid ordinary-input bridge are those of the complete parent. This
coordinate change introduces no new input promise.

## 4. Counts and degree bounds

Each changed core retains its certificate operations, removes one
comparison and one supplied coordinate, and saves one square plus two
additions in the final polynomial. This is **3 operations per core**.
The safe unit-product finalizer and all its factors remain in place.

| Strong treatment | Changed cores | Certificate | Comparisons | Witnesses | Polynomial | Degree upper bound |
|---|---|---:|---:|---:|---:|---:|
| Ordinary | geometry |258|13|50|296=141M+155A|1508|
| Ordinary | joint |258|13|50|296=141M+155A|3433|
| Ordinary | both |258|12|49|293=140M+153A|3440|
| Both normalized | geometry |262|11|50|294=143M+151A|2322|
| Both normalized | joint |262|11|50|294=143M+151A|3969|
| Both normalized | both |262|10|49|**291=142M+149A**|**3980**|

Both the four-program and independent fifth-duration-bound interfaces
have these counts. Conservative propagation includes all program
coordinates and uses only the inherited source-guarded cancellation
in each main norm. For the default source the product degree bound is
3892 and the remaining residual bound is44, giving3892+2*44=3980.
The two large X-bound residuals are gone, but the factors grow because
X now depends directly on r. No exact-degree or optimality claim is made.

## 5. Reproducibility and evidence limits

The receipt stores all twelve ledgers and complete polynomial schedules.
It checks unique topological definitions, guarded consumers and input
dependencies, literal M/A counts, and output reachability of every gate.
There are768 exact complete-source/output identities under(3),384 signed,
plus768 coordinate round trips and384 positive forward lifts. Fixed
numerals use consistent finite substitutions for these algebraic checks;
the actual enormous fixed constants retain their parent's exact recipes.

The scalar inverse checks include both signs in(5) and verify positivity
and inverse identities using exact integer exponentiation. They are
typed scalar fixtures, not numerical materializations of full positive
native Pell witnesses. The proof in Section3 supplies the global inverse
and universality; finite samples do not replace it.

```sh
python3 neary_woods_universal_positive_scale291.py
```

Author receipt generation and fresh replay pass. Independent full
proof/source review and fresh default replay pass without findings,
including the inverse on the shifted joint-index branch, guarded
dependencies and conservative degree propagation. A separate literal
executor checks192 complete source/output identities and coordinate
round trips across all twelve options,96 signed, with96 positive lifts.
All four local links resolve. These additional checks retain the same
algebraic scope; no giant positive Pell zero is numerically claimed.
