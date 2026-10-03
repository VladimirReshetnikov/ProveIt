# A forbidden input suffix gives a259-operation U9 polynomial

The [literal source](neary_woods_universal_lower_unit259.py) absorbs the last
ordinary comparison of the [260-operation parent](neary_woods_universal_history_units260.md).
The default is **259=133M+126A**, with258 certificate operations, one
comparison,43 positive witnesses, the same four positive program parameters
and degree **at most3861**. The separate fifth duration-bound interface is
also supported. The [receipt](neary_woods_universal_lower_unit259.json) stores
all selected emitted sources and their literal ledgers.

The positive zero sets are identical on every inherited valid program/input
slice. The supplied coordinates and fixed program recipes are unchanged.
The proof uses a property of the actual encoded input word, so it does not
assert the same equivalence for arbitrary invalid program parameters.
It preserves the full paid ordinary-input loader, exact initialization
counter, actual fixed U9 machine and universal slices. The established75
certificate and87 polynomial bounds are unchanged.

## 1. The paid lower factor

Retain the notation of the parent: b is the history radix, P=b^T after
typing, H_U,H_V the packed current values, N_U,N_V their selected affine
updates, U_f the final upper value, and V_f the paid terminal affine value.
The supplied positive program/input ports determine the loaded value V0.
The parent's last ordinary comparison is

    L_V=b*N_V+V0 = H_V+P*V_f=R_V.                    (1)

Both sides are already emitted. Define

    N_L=1+R_V-L_V.                                  (2)

Two additions/subtractions and one multiplication insert N_L into an
existing unit group. Delete comparison(1). At a zero of the grouped
polynomial every retained ordinary residual is zero and every integer
group product equals1; therefore every factor, including N_L, is1 or-1.
The finalizer uses either a sum of squared residuals or one unsquared
integer group times one plus a sum of squares, minus one. The latter
implication follows over integers even when the group is negative off zero.

The default parent has a single ordinary residual and a single unsquared
anchor G. It evaluates G*(1+(L_V-R_V)^2)-1. The new source evaluates
G*N_L-1 directly. It adds three certificate gates but removes the final
residual subtraction, its square, addition of1 and anchor multiplication:
the complete polynomial saves one multiplication. Its sole remaining
comparison is that the product of sixteen integer factors equals1.

The wrapper handles this empty ordinary-residual case explicitly. Its
polynomial is the emitted product minus1; there is no hidden multiplication
by1. For the degree audit only, a zero residual is passed to the inherited
propagator so its guarded main-norm cancellation remains applicable. This
adds no gate or comparison to the actual source. Other grouped schedules
retain the existing finalizer.

## 2. Typing before the lower transport

A new zero need not yet satisfy(1), and the existing global factor N_G may
also be-1. All the proof steps in Sections2--3 of the260 parent before its
final global-sign deduction remain valid. Here is their dependency order.

The equation N_G=+/-1 bounds the sum of six positive history coordinates
by P+1. It gives P>=5, every history/product hat strictly less than P,
and a positive history repunit with b<=P. These are exactly the weakened
pretyping bounds used by the parent's three strict computed-port margins.
The signed recoder mask relation supplies the unchanged low-port bounds.
Consequently the implicit four joint truth fields are positive, sum to the
joint scale minus1 and have residues(1,4,2,8) modulo16.

Independent local rank and step-down arguments recover every safe norm and
both linear factors, allowing a shifted geometry or joint index. The joint
index has residue1 modulo16; subtraction of2 strictly raises its population
beyond the available dyadic exponent. The paid loader congruence independently
excludes the negative geometry index. Thus both native indices have sign+1.
The dyadic recoder scales exclude the negative mask unit modulo2B-1.
None of these steps uses lower chronology or a relation among the newly
added factor signs.

The restored joined AND gives dyadic history b,P and P=b^T, a one-tile
selector in each row, all selected products, and row values in[0,D-1].
Here D is the paid height, with

    D=U_f+V0+V_f+height_slack,

and the fixed radix multiplier ensures every selected affine update is
strictly below b. Reducing the upper unit modulo b forces its sign+1:
its least digit lies below D<b-1 and cannot represent-1. The carry-free
upper transport is therefore fully restored. Every old native factor,
the mask unit and the upper unit now equals1. Only N_L and N_G could
still be negative.

This repeats the parent's local argument without its last total-product
step. That step cannot be used prematurely: the new factor may have changed
the global sign relation.

## 3. The negative sign would corrupt the initial word

If N_L=-1, equation(2) says

    b*N_V+(V0-2)=H_V+P*V_f.                         (3)

On a valid input, V0-2 is positive and below D. The same row bounds and
carry-free affine-history proof therefore decode(3) as the very same
selected tile sequence, but with lower initial sentinel V0-2. This is an
arithmetic consequence of the sign, not an assumption that the altered
word lies in a valid simulation slice. The upper initial sentinel is1,
its final value is U_f, and the lower endpoint is still

    V_f=2^(beta+1)*U_f+2^beta,

the result of appending the fixed terminal word10^beta.

The [four-tile word theorem](binary_tag_four_tile_history.md), Section1,
uses upper words1 or10^beta1. Its valid lower input is the positive
sentinel of

    E(w)=e(w without its final b)10^beta,
    e(b)=10^beta1, e(c)=1, beta>=2,

where w ends in b. Let P0 be the sentinel of e(w without its final b).
Every e-image ends in1, and the empty prefix has sentinel1. Hence P0 is
positive and odd, and the binary expansion of V0 is

    V0 = [binary(P0) 1 0^beta].                    (4)

Subtracting2 gives exactly

    V0-2 = [binary(P0) 0 1^(beta-1) 0].             (5)

Because beta>=2 and P0 ends in1, the newly inserted zero is an internal
zero run of length1, equivalently an occurrence of101. Appending any
lower tile words cannot remove that internal occurrence. This includes
the singleton input w=b, when P0=1.

On the upper side, the initial sentinel is1, each tile appends either1
or10^beta1, and the terminal appends10^beta. Every zero run in the complete
upper binary string has length exactly beta. In particular it contains
no101. Equality with the lower binary string beginning with(5) is
impossible. Positive binary sentinels have unique expansions, so this
contradicts the decoded endpoint equality.

Thus N_L=+1 at every new zero on a valid program/input slice. Once this
sign is restored, all factors except N_G are1; its group product then
forces N_G=1 as well. Both(1) and the entire260 parent polynomial are
restored on the identical supplied tuple.

Conversely, every positive260 zero on the same valid slice has all its
factors equal to1 and satisfies(1). Hence N_L=1 and every new group product
and retained comparison holds on that same tuple. This proves equality
of the positive zero sets on valid slices, in both directions. The earlier
260-to263 slack bijection is unchanged; no additional slack shift or
fresh native witness is needed here.

The ordinary-input conclusion is not obtained by asserting a word property
for arbitrary parameter tuples. The restored recoder and unchanged actual
loader provide exactly the inherited valid encoded word ending in b and
its least-dyadic initialization counter. This source retains all conditions
which pay that interface. With an invalid program tuple, the forbidden-word
hypothesis might fail; no all-parameter equivalence is claimed.

## 4. Counts, degrees and exact arbitrary-point corrections

The default certificate is258=133M+125A with one comparison and43 positive
witnesses. Subtracting1 from its single product gives259=133M+126A.
The new factor has propagated degree at most5. The old unit product has
bound3856, so the new product has bound3861; the parent's lower-residual
square no longer adds10 to that product's degree. These are upper bounds,
not claims that the exact polynomial degree equals the bound.

For other parent schedules the added three certificate gates usually
exactly offset the deleted comparison's finalizer cost. A one-group,
fully normalized anchored source with no other ordinary comparisons gets
the additional one-operation saving. The wrapper can place N_L into any
old group and chooses the least propagated degree among those placements.
The receipt's schedules are images of selected260 schedules, not an
exhaustive partition search over the enlarged factor set. Several have
worse degree bounds than their retained-comparison parents; the parent
remains available. The mapped270/608 schedule has44 witnesses, while the
fixed43-witness267/1344 schedule is unchanged in those counts.

Let r=L_V-R_V and G_j be the old group values on an arbitrary integer
assignment. Put M_j=N_L for the chosen group and1 for every other group.
All old emitted registers are literally unchanged. For an all-SOS output,

    P_new=P_old-r^2+sum_j((G_j*M_j-1)^2-(G_j-1)^2).

For an unsquared anchor a, put
C=sum_(j!=a)((G_j*M_j-1)^2-(G_j-1)^2). Then

    P_new=M_a*(P_old+1)+M_a*G_a*(C-r^2)-1.          (6)

These are polynomial identities, including signed assignments and zero
factor values. They apply to the empty-residual finalizer too. They are
not an assertion that the old and new off-zero polynomials are identical.

The guard reconstructs the whole frozen260 caller, including every outer
row, domain, numeral role, active nested interface, group and ledger. It
checks the exact lower sides and comparison and fresh temporary names.
All old registers and exports remain available; none is erased. Every
new group product is checked against its indexed factor list, and every
emitted gate must reach the final output.

## 5. Reproduction and audit scope

```sh
python3 neary_woods_universal_lower_unit259.py
```

The receipt records124 source/degree/count ledgers:32 one-group base/interface
choices plus92 group placements in44 distinct selected parent/interface
sources. The sixteen bases cover all inherited strong treatments and
positive-scale choices. It saves44 selected complete emitted sources and
checks992 complete register/group/final-output corrections,496 signed.
Seven incompatible callers exercise the source/domain/interface guards.

Finite word audits cover2,805 valid sentinels at beta2 through12, including
singleton b;14,025 appendings preserve the forbidden internal101; and1,397
upper tile words lack101. These check the exact finite-string mechanism,
not native Pell zeros or materialized universal machine constants. The
unbounded forbidden-subword argument and the full inherited native/loader
proof supply the theorem.

Author receipt generation and a fresh default replay pass. Root independently
reviewed the full proof, source and inherited dependencies and passed a fresh
default replay. Its own executor checked256 complete outputs,128 signed,
across32 canonical base/interface contexts, including every retained row;
1,040 appended-sentinel cases covered four further widths and odd P0 from1
through129. Franklin independently reviewed the full proof/source and passed
a fresh default replay. His own executor checked240 complete grouped outputs,
120 signed, across30 placements and both bound interfaces;320 new sentinels,
1,280 actual affine lower appendings and425 actual upper tile words also passed.
These word/algebra fixtures are not full native Pell zeros. Both reviews found
no remaining issue. All four local links and whitespace checks pass. The trio
is frozen; no frozen parent, shared navigation or Git state is modified by it.
