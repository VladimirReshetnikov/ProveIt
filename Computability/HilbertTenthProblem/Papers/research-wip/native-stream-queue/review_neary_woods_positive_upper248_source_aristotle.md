# Independent source review of the positive-upper248 construction

**PASS for the complete source, affine pullback, interfaces and accounting.**
Both sources cost248=129M+119A with43 positive witnesses. The sole gate
saving is one subtraction. The total degree bound936 transfers from the
corrected geometry-only249 parent by an affine substitution. This review
does not replace root's separate proof that the two coordinate shifts
preserve the complete positive-zero domain.

## 1. What was read and checked

I read the full314-line frozen mathematical note and209-line helper inertly, all248 producer
definitions of the first interface, and the complete difference to the
second interface. The fresh independent checker reconstructs every producer
definition in both arrays from the actual frozen geometry-only249 parents,
checks the submitted ordering separately, and compares all496 records.
It neither executes nor symbolically propagates a source array.

The complete249 parent proof, its required degree correction, the250 proof,
and all parent arrays were already read in my preceding249 review. Their
exact bytes are authenticated again, without repeating the older native
proof audit. For this review I additionally read the four-tile note
lines1--135 and165--200 and the250 note lines1--110 to bind the tile order,
upper affine form and fixed input interface. The parent's valid-program,
machine, input-loader and native/Pell theorems remain inherited. The
author's finite cut/scalar/word evidence was read as evidence, not replayed.

## 2. Independent manual affine identities

Let Z be the new positive `hist__ZU0` and G the new positive
`hist__global_bound`. The proposed parent coordinates are

    ZUhat_old=Z+1,  global_bound_old=G-1.                (1)

All other supplied coordinates are identical. At these formal values,
the parent's global sum equals the child's exactly:

    HU+HV+(Z+1)+ZVhat0+ZVhat1+(G-1)
      =HU+HV+Z+ZVhat0+ZVhat1+G=P.                     (2)

The three intermediate global sums differ by1, but they feed only their
successor and then P. The source audit guards those complete consumer
chains, so the equality at P contains every exit of that changed cone.

Put A_u=2^(beta+2), d_u=A_u-2 and o_u=2^(beta+1)+1. These are fixed
compiler numerals, not extra variable ports. From the actual tile slopes
and offsets the upper affine sum in unhatted selectors is

    2HU+d_u*Z+(S0+S3)+o_u*(S1+S2).

Replacing S_i by Shat_i-1 subtracts the fixed correction
2+2o_u=A_u+4. Hence the new upper constant is exactly2^(beta+2)+4.
If Z is also hatted, the correction additionally includes d_u, giving
2A_u+2=2^(beta+3)+2, the parent's literal recipe. Therefore

    C_old=C_new+d_u,
    d_u*(Z+1)-C_old=d_u*Z-C_new.                       (3)

This is an independent derivation of the changed numeral recipe, not a
test at a small substitute beta. The actual fixed U9 beta and all other
recipe data stay identical. No runtime gate constructs C_new from C_old;
the same multiplication by d_u and subtraction of its fixed constant are
still charged. The upper_constant role has exactly one consumer,
`hist__linear_constant__168`.

For the packing identities write H_i=hist__Shat_i, V_i=hist__ZVhat_i,
C=P*(H0+P*H1), D=P*(V0+P*V1), and T=P²+P. Then

    (H1+H2-1)+C-(T+1)=(H1+H2-2)+C-T,                 (4)
    (Z+1)+D-(T+1)=Z+D-T.                             (5)

The value H1+H2-2 is the already paid `tree_group12`. Thus deleting the
private H1+H2-1 producer and changing the shared tail to T preserves both
pack exits. Its consumers are exactly `hist__unhat_pack__65` and
`hist__unhat_pack__74`; neither changed tail nor numerator leaks elsewhere.
The controller still uses the same tree_group12 and the same Ctree value.

Equations(2)--(5) cover all four exits: P, Ctree, selected-word pack Zb,
and the upper linear form. The independent consumer audit also guards
every intermediate global/upper-linear/pack sum whose value changes.
Every other row definition is retained, so structural induction through
the remaining graph gives the all-ring equality

    F248(new)=F249_geo(ZUhat=Z+1,global_bound=G-1,others),

with C_old=C_new+d_u included in the fixed-coefficient substitution.
This is not an identity for independent arbitrary choices of both upper
constants, nor a claim that every retained intermediate value is identical.

## 3. All rows, cost and both fixed-program interfaces

Exactly one producer is deleted:

    hist__group_hat__59=hist__group_sum__58-1.

Exactly five retained records change: global_sum__12,
linear0_coefficient__17, pack_sum__63, repunit_tail__64 and pack_sum__73,
all with the `hist__` prefix. There are no new producer names. The remaining
243 records are literal parent records. This syntactic number includes
`hist__linear_constant__168`, whose upper_constant numeral has the explicitly
changed value in(3). It must not be described as243 unchanged numerical
definitions. Reordering to make tree_group12 available costs no gate.

Both complete arrays pass independent topology and backward-liveness checks.
Every row, all43 witnesses and all eleven fixed-numeral roles remain live.
The default merged interface has ordinary positive input x and four fixed
program parameters program_A,program_B,program_T,program_E:48 total supplied
ports. The separately bounded interface adds fixed program_bound:49 ports.
The only producer difference between those two arrays is
program_duration_bound, using program_E or program_bound respectively.
No program numeral is recategorized as a witness or ordinary input.

The43-name auxiliary list changes only ZUhat0 to ZU0, with the `hist__`
prefix. The domain metadata is the unchanged generic positive-integer
declaration and contains no stale old-name restriction. Old ZUhat names
survive only in explicitly labeled parent-delta and inverse metadata.
The entire fixed U9 recipe and ten other fixed-numeral recipes are literal
unchanged; the program's shifted-input convention is inherited intact.

The final product spine retains all15 paid multiplications, with precisely
the same16 factor leaves appearing once each. It ends with subtraction of
the already paid geometry discriminant geo__A. Its producer certificate is
247=129M+118A with one comparison to geo__A; the complete source adds its
last subtraction, yielding248=129M+119A. No comparison, loader, selected
history, native relation, or terminal product is dropped from the count.

The required249 correction gives bound936 for these geometry-only parents.
The invertible affine substitution(1), at the related fixed constant
recipes, cannot increase total degree on a fixed program slice. This proves
the child's stated upper bound without degree propagation. The superseded
934 claim is not used, and no exact-degree or global minimality claim follows.

## 4. Positive-domain boundary and evidence limits

The formal inverse(1) need not be positive at an arbitrary positive child
tuple: G=1 gives old global_bound=0. Conversely an arbitrary old positive
tuple may have ZUhat=1 and hence new Z=0. The author's numbered remarks
correctly preserve these distinctions. An all-positive-zero equivalence
requires the separate language proof that old zeros have ZUhat>1 and the
independent child typing proof forcing G>=30. Root owns that semantic
challenge. The source equality and accounting above do not infer those
facts merely from the affine identities or finite word samples.

The final author's numbered Remarks3--4 retain two draft scope corrections:
matching-history existence is conditioned on acceptance or a zero, and
the deduction that the normalized parent factors are units starts at a
child zero. Those repairs are present in the final bytes reviewed here.

No author/predecessor helper, saved source array, compiler or builder was
executed or imported. Only the newly authored static reviewer was run
before freezing; it checks bytes, record definitions, consumers, graph
ordering/liveness, roles and product-spine syntax. It has no arithmetic
source interpreter or degree propagator. After freezing it is evidence
only and must not be replayed. No repository or Git mutation occurred.

## 5. Frozen bindings

The author files below have stem `/tmp/neary_woods_positive_upper248_tesla`.

| Artifact | SHA256 |
|---|---|
| Author MD | f3329cf28090e39a219ac4e3d8882b99fc5bab72ae0507647a193cbdb514d557 |
| Author PY, read inertly only | ad9eb9991205261172cfd8e09537c75c05b153b3431b224ac1d4744319277d92 |
| Author JSON | bab6ba8d61e9fac494ca42124b043c358597d19bf1ebf8f8699b2c054ff476bc |
| Fresh reviewer `check_positive_upper248_static_aristotle.py` | cd4f9d2ad266675736c012c560eb134b7097986b38d989a00a4fa9e008c020b8 |
| Fresh evidence `positive_upper248_static_read_aristotle.json` | 2b80d0541ad96f29f874b2ace7cc45f4fa319991680b574045565255501180ac |

The fresh reviewer's normal and optimized runs from `/` passed before
freezing and produced byte-identical static receipts. These checks cover
all496 child definitions, the two parent interfaces, eight dependency pins,
and all affected consumers and final product rows. There was no scientific
replay of the author's four polynomial cuts or bounded scalar diagnostics.
The companion review JSON binds this note, these frozen artifacts and the
precise additional source-read spans.
