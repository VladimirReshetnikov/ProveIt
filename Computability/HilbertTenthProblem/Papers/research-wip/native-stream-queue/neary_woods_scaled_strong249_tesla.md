# Scaled strong sharing in the complete U9 compiler: 249 operations

The complete hierarchical U9 compiler has a **249 = 129M + 120A**
successor with the identical **43 positive witnesses**, ordinary positive
input and fixed program interfaces. Scaling only the geometry strong
factor gives total degree **at most 934**. Its positive zero set is
identical on all supplied coordinates to that of the pinned250 source;
no native coordinates need replacement. Existential history length remains
unbounded and fully compiled.

The geometry-only, joint-only and both-core changes each cost249. The
latter two have the larger degree bounds1038 and1046. Both program
interfaces are emitted for each change, giving six complete source
arrays. This transfers the coefficient sharing from the existing84
construction into an alternative universal host. The separate overall
universal84 bound is unchanged.

## 1. Actual source cut and its complete identity

For either native prefix `geo__` or `and__`, abbreviate the actual registers
as

    c=R10a, a=R12, Delta=A, c2=c*c, Ac2=Delta*c2,
    L16=f*f, V=of-c, y=y_aux.

Here the register `A` is the discriminant `a*a+4*a+3`, not the Pell
parameter. The main norm already pays for `c2` and `Ac2`, and all their
other consumers remain. The parent auxiliary coefficient and strong
factor are

    t=i*c2, Qs=Delta*t*t, Kaux=Delta*Qs,
    Ns=f*f-Qs, Na=Kaux*(V*V-y*y)+y*y.                 (1)

The exact private five-row parent block is

    ic2 = i*c2
    ic22 = ic2*ic2
    normalized_strong_Q = Delta*ic22
    f_square_minus_one = L16-normalized_strong_Q
    R16 = Delta*normalized_strong_Q.

It costs4M+1A. Replace it by the four rows

    scaled_aux_root = i*Ac2
    R16 = scaled_aux_root*scaled_aux_root
    scaled_f_square = Delta*L16
    f_square_minus_one = scaled_f_square-R16.        (2)

This costs3M+1A, and the following identities hold over every commutative
ring on the identical independent coordinates:

    Kaux_new=(i*Delta*c*c)^2=Delta^2*i^2*c^4=Kaux_old,
    Ns_new=Delta*f*f-Kaux_new=Delta*Ns_old,
    Na_new=Na_old.                                   (3)

The actual auxiliary expression uses the retained `V=of-c` and its square;
it is not replaced by a free norm coefficient. The removed `ic2` has only
`ic22` as a consumer, `ic22` only `normalized_strong_Q`, and the latter
only the strong subtraction and `R16`. Each strong factor occurs exactly
once in the complete product spine. The fresh static receipt checks these
consumer sets, all eight paid definitions including `c2,Ac2,L16`, and
the literal retained rows of both parent interfaces.

Let `F250` denote the actual complete product of the sixteen parent
factors minus1. Write `Delta_g,Delta_j` for the geometry and joint
discriminants. For one scaled core change only the final subtraction
from1 to its already paid discriminant. For both cores also pay for
the single multiplication `scaled_discriminant_product=Delta_g*Delta_j`
and subtract that product. Then the complete source polynomials satisfy

    F249_geo   = Delta_g*F250,
    F249_joint = Delta_j*F250,
    F249_both  = Delta_g*Delta_j*F250.                (4)

No equation, typing, division or on-zero simplification enters (3)--(4).
All unaltered norm, input, index, transport, loader and history rows have
the same values as in250. The changes in (3) affect no other producer,
so the cut identities lift to the complete saved sources. A stable
topological reorder makes the new dependency of the strong factor on
`R16` explicit.

## 2. Positivity on the entire supplied positive domain

Cancellation in (4) must precede invocation of any parent zero theorem.
In particular, positivity of the joint discriminant cannot be borrowed
from the recovered AND fields or decoded history. The actual retained
loader proves it directly, as follows.

Let `d0` be the fixed positive `repunit_divisor`, `r0` the fixed positive
`recoder_radix`, and `ch` the fixed positive `history_radix`. The valid
compiler recipes give these properties; no further relation between
these three numerals is needed in this section. All supplied input,
program and witness coordinates are strictly positive integers.
Abbreviate the actual prefix by

    duration=program_bound+program_duration_gap,
    I=x+duration+input_slack,
    load_r=I+z+power_gap,
    M=d0*load_r, Q=M+1, B=r0*Q,
    Jd=(B-1)*duration_quotient+duration,
    Pr=(B-1)*Jd+1,
    scale=I*Pr, q0=16*B*scale.                       (5)

The default merged interface uses `program_E` instead of `program_bound`
in the first line. In either interface `M>0,Q>=2,B>=2,Jd>0,Pr>0,q0>=16`
before imposing any residual. The geometry core literally uses

    Rg=d0*Jd,
    Xg=Q*(Rg+geo__bound_beta),
    Yg=(2*geo__odd_half+1)*Q,
    ag=Yg*(Xg+1), Delta_g=ag^2+4*ag+3.              (6)

Thus `Xg,Yg,ag` and `Delta_g` are strictly positive.

For the joint core set `D=hist__height_slack>=1`, `b=ch*D>=1`, and

    P=H_U+H_V+ZUhat0+ZVhat0+ZVhat1+global_bound>=6,
    Si=Shati-1>=0,
    Ctree=(S1+S2)+P*S0+P^2*S1>=0,
    Zb=(ZUhat0-1)+P*(ZVhat0-1)+P^2*(ZVhat1-1)>=0,
    Hr=H_U+P*H_V>0,
    Zhigh=Zb+P^3*Ctree+P^6*Hr>0.                    (7)

These are all-value identities for the actual hatted packs. They need
neither `P=(b-1)J+1` nor a selector subset condition. In particular they
hold when all four unshifted selectors vanish. The actual lower output
field and joined scale are

    lowF3=16*B*(M*(quotient_hat-1)+z)+8>0,
    F3=lowF3+q0*Zhigh>0,
    q=q0*b*P^8>=16.                                  (8)

Here `quotient_hat>=1`, so the expression inside the first parentheses
is positive independently of any quotient equation. The source's
`factored_pack_Z` and joint tail-bound rows now give

    Z0=(q-1)*F3>=0,
    Xj=q*(Z0+and__bound_beta)>0,
    Yj=(2*and__odd_half+1)*q>0,
    aj=Yj*(Xj+1), Delta_j=aj^2+4*aj+3>0.             (9)

For each core `Delta=(a+1)(a+3)>=8`. This proof uses only the displayed
retained positive prefixes. It does not assume positive implicit
`F0,F1,F2`, dyadic scales, a signed repunit factor, norm signs or any
history equation. Those more demanding parent pretyping obligations
are recovered only after cancellation in (4).

## 3. Exact zero tuples, factor semantics and universal interface

Over the integers, (4) and the unconditional strict positivity in
Section2 imply

    F249_geo=0 iff F249_joint=0 iff F249_both=0 iff F250=0

on the entire positive supplied domain of either inherited valid
program interface. The same input, fixed program tuple and all43
witnesses work in both directions. This is stronger than a projection
with fresh native completion: the complete positive zero tuples are
identical. It requires no norm-rank reproof or choice of new Pell roots.

After this cancellation, the accepted250 theorem applies with its
unchanged signed pretyping, hierarchical selector, ordinary-input,
duration, chronology and terminal arguments. For every recursively
enumerable set S of positive integers, the same effective valid shifted
four-parameter program tuple `(A_S,B_S,T_S,E'_S)` satisfies

    x in S iff there exist w1,...,w43>0:
        F249_geo(x,A_S,B_S,T_S,E'_S,w1,...,w43)=0.   (10)

The optional separately bounded interface retains the same inherited
fifth fixed program parameter. Its semantics is likewise unchanged.
The fixed program parameters are not existential witnesses. No input
exponent, word, program loader, control sequence or iteration is made
free by this change. The exact eleven fixed-numeral recipes are copied
from the parent, with each use still paid.

**Remark 1 (scaling is not an unrestricted zero-set equivalence).**
At independent factor ports take `Delta=0`, remaining-factor product
`U=0` and old strong factor `Ns=1`. Then `U*Ns-1=-1`, whereas
`U*(Delta*Ns)-Delta=0`. These are formal factor-port data, not a full
source assignment or a positive compiler zero. They refute any inference
of unrestricted signed zero-set equivalence from the all-ring identity
alone; Section2 supplies the necessary missing hypothesis here.

**Remark 2 (the new factors are not all units).** A product equal to a
positive discriminant does not by itself force its factors to be units:
the integer factors2 and4 have product8. In this construction cancel (4)
first. The recovered parent theorem then gives all parent factors+1.
Every unscaled factor remains+1; a scaled strong factor equals its
discriminant, rather than1. For both scaled cores the product equals
`Delta_g*Delta_j`. The receipt's `parent_factors_historical` is retained
provenance, not an assertion that the modified factors are sixteen units.

## 4. Six complete ledgers and degree bounds

One scaled core saves1M. Scaling both saves2M in the cores and adds1M
for the final discriminant product. The final subtraction still costs1A.
No row in either complete source is dead, and every supplied parameter,
witness and fixed-numeral role remains live. The ledgers are

| Program interface | Scaled cores | M | A | Total | Positive witnesses | Degree upper bound |
|---|---|---:|---:|---:|---:|---:|
| Four fixed parameters, plus input | Geometry |129|120|249|43|934|
| Four fixed parameters, plus input | Joint |129|120|249|43|1038|
| Four fixed parameters, plus input | Both |129|120|249|43|1046|
| Five fixed parameters, plus input | Geometry |129|120|249|43|934|
| Five fixed parameters, plus input | Joint |129|120|249|43|1038|
| Five fixed parameters, plus input | Both |129|120|249|43|1046|

Each certificate before its final subtraction costs248=129M+119A and
has one product comparison. For a single scaled core,244 parent rows
are literal, three are deleted, three are edited and two are added.
For both cores,239 parent rows are literal, six are deleted, five are
edited and five are added. Stable ordering introduces no arithmetic.
There are1494 emitted rows across all six arrays.

The parent manual all-value degree bound is926. All supplied coordinates,
including the program ports, have degree1; fixed compiler numerals have
degree0. Directly from (5)--(6), `deg q0<=5`, `deg Xg<=3`,
`deg Yg<=1`, `deg ag<=4` and `deg Delta_g<=8`. Equations(7)--(9)
give `deg Zhigh<=8`, `deg F3<=13`, `deg q<=14`, `deg Z0<=27`,
`deg Xj<=41`, `deg Yj<=15`, `deg aj<=56`, `deg Delta_j<=112`.
The complete identities (4) therefore give the three bounds

    926+8=934, 926+112=1038, 926+8+112=1046.

This is a manual polynomial-product argument, not degree propagation
through a saved array. It does not assert exact degrees or global
optimality. Geometry-only is the best degree bound among the three
equal-cost variants here; scaling both is not a248-operation result.

## 5. Read and evidence scope

The complete pinned250 proof (438 lines), both complete250 arrays and
their JSON metadata (3945 lines), and the complete84 scaled-strong proof
(147 lines) were read inertly. The latter supplies the prior sharing
route; its helper and examples were not executed. Parent universality
and its external simulation/Pell dependencies are inherited through the
accepted250 theorem, not newly audited from the literature.

The fresh helper authenticates the three dependencies below, statically
edits both source arrays into the six variants, and checks exact private
consumer sets, full topology, counts, retained rows, all supplied-port
liveness and all eleven fixed-numeral roles. It has no saved-array
interpreter or degree propagator. Its sparse arithmetic checks five
independently handwritten polynomial cut identities, including the
unchanged auxiliary norm and the complete one-/two-core finalizers.
It separately checks64 handwritten positive-prefix contexts, including
32 with all unshifted selectors zero and contexts with numeral1 and
height1. Those are prefix diagnostics, not full native/compiler zeros
or substitutes for the general positivity proof.

No archived, supplied, frozen or predecessor program was executed or
imported. No parent or emitted source array was evaluated. Only the
fresh helper's own structural and handwritten-cut diagnostics run
before freezing. Independent reviews are separate records.

The fresh writer and separate normal and optimized (`-O`) exact receipt
checks ran from `/` and passed before freezing. The helper has213 lines;
the six-source receipt has11208 lines. Their filenames are
`neary_woods_scaled_strong249_tesla.py` and `.json`, with SHA256
`ba382dda0e52d6821a5808a3dcc92fb45c4e8bbf0b5e1c2510b9b607ccea21ad`
and `e8fb322a18ec77cf9936ebb7d9e25d86414b66f8db561c4a64edb2ef16aba35c`,
respectively. These checks authenticate source structure and independent
cut formulas only; they are not native-array replays.

| Dependency | SHA256 |
|---|---|
| `neary_woods_hierarchical_history250_tesla.json` | `d2f1ae7870cb8ec295d4401a8e9c951047f0e92cf2b6e6f4bb723c6b483f1ebf` |
| `neary_woods_hierarchical_history250_tesla.md` | `1bb41ed9eae9e77b2a9236c49508a55538f2ff84d1cd245f3bccec4dee39a330` |
| `complete84_scaled_strong_output.md` | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |
