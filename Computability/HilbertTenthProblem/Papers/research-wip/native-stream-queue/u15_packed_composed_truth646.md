# Composing state relabeling and computed truth fields gives 646 operations

The complete ordinary-input polynomial now costs **646 = 252M + 394A**,
with **46 comparisons and 102 positive witnesses**. The raw natural
half-tape polynomial costs **403 = 144M + 259A**, with 11 comparisons
and 51 positive witnesses. The [compiler](u15_packed_composed_truth646.py)
composes the frozen [652 state relabeling](u15_packed_state_relabel652.md)
and [647 tagged truth-field projection](u15_packed_computed_truth647.md).
All arithmetic, the input loader, typing, comparisons and finalizers are
emitted in the [receipt](u15_packed_composed_truth646.json).

| Interface | Certificate | Comparisons | Positive witnesses | Complete polynomial |
|---|---:|---:|---:|---:|
| Natural initial half tapes |371 = 133M + 238A|11|51|403 = 144M + 259A|
| Ordinary positive input |509 = 206M + 303A|46|102|646 = 252M + 394A|

The four fixed positive program numerals and the complete valid-program
universality theorem are unchanged. The frozen compiler metadata retains its
inherited formal degree upper bound1936. The [separate degree audit](u15_packed_exact_degree1936.md)
now proves that degree1936 is exact for every fixed program quadruple.
This does not establish optimality or change the global87-operation bound.

## 1. Guarded composition of actual complete sources

All three source files are checked before importing either parent:

| Source | SHA256 |
|---|---|
| Baseline653 |`ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318`|
| Relabel652 |`cd3904fb083d1a254461ffde87636a6b9014bcdecb1db48cfcf2f30f41493879`|
| Computed truth647 |`c363ea0679825559d5247608f748d877e75146dbb997b159db42294d9d676eb7`|

The constructor obtains complete canonical packets from both parents. The
652 import context isolates sibling module names, and the 647 parent also
checks its fixed type-tagged hashes of the actual raw and ordinary baseline
packets. A cached foreign loader cannot supply different arithmetic behind
the correct source-file hashes.

The constructor then copies precisely the frozen 647 `_tagged` and `_child`
function ASTs into fresh globals. Their parent adapter supplies a defensive
copy of the canonical 652 packet and the pinned baseline's actual finalizer.
It rebuilds the tagged parent and child in full. The copied transforms retain
their row/comparison layout guards. Metadata records the actual 652 source
and packet hashes, all three source-lineage pins, and the B/J code permutation.
It does not present a transformed packet as a canonical output of the 647
public API.

The resulting tagged parents cost 412 raw or 655 ordinary. They have the
same certificate costs as their children, but retain the three positive
truth coordinates and three graph comparisons. Removing those comparisons
saves exactly three residual subtractions, three squares and three summation
additions. The three tag operations and all five field-definition operations
remain charged.

## 2. Positivity and the exact graph parent

Use the common outer registers and equations

    J = sum_i(edge_i-1), D=L0+R0+height, B=64D,
    P=(B-1)J+1, T=P^34, cap=B*T,
    B*U=S+P,
    H+G+ZL+ZR+ZU+bound=P.

The relabeling affects only the Q and N state projections and their terminal
coefficient. It does not affect these expressions, the head equation, aggregate
bound, joined native ports or input loader. Consequently the complete
pretyping proof of 647 applies without any new hypothesis: before AND or
power typing, positivity and the two displayed retained equations give

    B>=64, J>0, P>=B,
    H,G,ZL,ZR,ZU<P, U<=J<P,
    0<=A,M,Z<T,

where A,M,Z are the original joined words. The selector coefficients in S
and Dir are still 0 or 1, so `S,Dir<=J`, `(B-1)Dir<=P-1`, and the copied
range mask remains below P. Every joined lane is therefore canonical before
native typing. The state-transport equation is not used in these bounds.

Pay the same three tag operations:

    A'=A+2T, M'=M+T, Z'=Z, cap'=cap.

With padded native ports `padded_A=16A'+12`, `padded_B=16M'+10`,
`F3=16Z+8`, and `q=16cap`, reconstruct

    F1=padded_A-F3,
    F2=padded_B-F3,
    F0=q-padded_A-F2-1.

These are exactly the parent's five subtraction gates. Their closed forms
and pretyping lower bounds are

    F1=16(A'-Z)+4 >=16(T+1)+4,
    F2=16(M'-Z)+2 >=18,
    F0=16(cap-A'-M'+Z)-15 >=16((B-5)T+2)-15>0.

Thus the restored coordinates satisfy the original positive native contract
before that contract is invoked. This positivity does not assume an already
typed AND output or a canonical Pell witness.

Let rho restore these three computed coordinates and retain every other
coordinate. The three omitted tagged-parent residuals are exactly

    F0+F1+F2+F3+1-q,
    F1+F3-padded_A,
    F2+F3-padded_B.

They vanish identically under rho. The symbolic source audit compares all
other registers and comparisons after restoration; it also proves each
removed residual zero by exact affine algebra in the opaque ports. Hence,
for **every signed integer assignment v**, the complete polynomial identity
is

    F_646(v) = F_tagged_relabel_parent(rho(v)).

The raw interface has the analogous 403/412 identity. This concerns entire
emitted SOS polynomials, including the full retained strong native auxiliary
residual. No equation valid only at a zero is substituted into that residual.

At a new positive zero the retained head and aggregate equations hold, so
rho restores positive coordinates and yields a tagged-parent positive zero.
Conversely the tagged-parent graph comparisons uniquely determine the three
fields. Erasure and restoration are inverse on the complete positive zero
sets. This is a graph bijection with the **freshly tagged 652 parent**.

## 3. Exact relation to 647 and to the untagged baseline

The 646 and 647 compilers have the same parameters and supplied witnesses.
Their new tagged ports, computed truth fields and all native comparison
polynomials are identical on arbitrary integer assignments. The symbolic
audit checks every nonstate comparison: 10 raw and 45 ordinary.

Their only changed comparison is state transport. The code permutation

    (A,...,O) -> (0,9,2,3,4,5,6,7,8,1,10,11,12,13,14)

fixes the initial A code 0 and sends the halting J code 9 to 1. Once the
common native equations type the same original rule-index word, the old and
new state equations have exactly the same chronological meaning. Both use
codes in 0,…,14 and B>=64, so successive reduction modulo B recovers each
state equality without carries. Injectivity of the permutation makes the
old and new adjacent-state and terminal conditions equivalent.

Therefore 646 and 647 have the **same complete supplied-positive zero set**,
with the identity map on all supplied coordinates. Raw tape parameters remain
natural; all raw auxiliaries are positive. The ordinary coordinates retain
their positive domain and the same four fixed program numerals.

There is also an exact off-zero correction. In the unchanged original rule
order put `E_i=edge_i-1` and let B,P be the common outer registers. Direct
sparse affine expansion of the emitted Q and N projections gives

    Q_646-Q_647 = 8(E2+E3-E18),
    N_646-N_647 = 8(E0+E23-E17).

Writing

    R=B*N_647-Q_647-9P,
    Delta=8[B(E0+E23-E17)-(E2+E3-E18)+P],

one has on every integer assignment

    F_646-F_647 = Delta*(2R+Delta).

These polynomials are not identical off zero.

The relation to **untagged652** is different. Paid native typing gives that
cap=B*P^34 is dyadic, hence B,P and T are dyadic. Since A,M,Z<T, the high tags
2T and T are disjoint and

    (A+2T) AND (M+T) = A AND M.

Thus the tagged and untagged predicates have the same outer positive relation.
Their native input ports and packed truth index differ. Passing between them
uses fresh full positive extensions for **all history native coordinates**;
it does not retain an old untagged Pell witness. The entire ordinary loader,
including its own recoder witnesses, remains unchanged. No graph identity to
untagged652 is asserted.

The complete unbounded first-halt and ordinary-input theorems follow by these
three precise relations: graph bijection to the fresh tagged parent, the
same supplied-positive zeros as647, and native-extension equivalence to the
untagged baseline. No horizon, lookup oracle, tape-typing assumption or
omitted arithmetic operation is introduced.

## 4. Public interfaces and replay

The public APIs mirror the graph interfaces of 647 and accept an optional
`root` keyword:

    build(ordinary=False, *, root=None)
    tagged_parent(ordinary=False, *, root=None)
    checked(packet, *, root=None)
    checked_tagged_parent(packet, *, root=None)
    evaluate(packet, values, *, signed=False, root=None)
    evaluate_tagged_parent(packet, values, *, signed=False, root=None)
    lift_to_tagged_parent(packet, values, *, signed=False, root=None)
    project_from_tagged_parent(packet, values, *, signed=False, root=None)
    polynomial_source(packet, *, root=None)

The sibling layout works by default. During isolated review, `--root` points
to the directory containing the pinned baseline; the two transfer parents
may sit beside this file or in that root. Every public call rechecks the
three source pins. Canonical packets and polynomial sources are defensive
copies, exact Boolean flags are required, and packet comparison preserves
exact scalar/container types. The parent coordinate validator preserves
natural raw tapes, positive witnesses and the positive ordinary interface.

Positive graph helpers require the retained head and aggregate equations.
Signed restoration is defined on every exact integer tuple; projection still
requires the three graph equations. These helper contracts do not promise
positive restoration for arbitrary positive false witnesses outside the
proved pretyping cone.

Run from any directory:

    python /path/to/u15_packed_composed_truth646.py --root /path/to/native-stream-queue

The default compares the adjacent receipt and writes nothing. Only `--write`
refreshes it. The research verifier requires assertions enabled; source pins
and public validation use explicit exceptions.

The author writer checks both complete compilers and both tagged parents.
Its exact source audits establish 870 restored register identities, 57 retained
comparison identities, six zero deleted comparisons, and 55 unchanged comparison
identities against647. It independently verifies the four changed affine Q/N
maps. There are 128 complete graph identities and 128 complete relabel output
corrections, including 64 signed tuples; 16 genuine positive outer restorations;
1,184 malformed public-object rejections; six defensive-copy checks; and two
cold poisoned-loader isolation tests.

The genuine histories check all outer comparisons and exact joined AND,
and reconstruct positive truth fields. The other native coordinates are
placeholders, so these are not materialized complete Pell zeros. The all-value
extension and positivity proofs supply the unbounded claims.

The writer and fresh default replay passed, including after repository placement.
The [independent composition review](review_u15_composed646.md),
[checker](review_u15_composed646.py) and [receipt](review_u15_composed646.json)
confirm the complete source, positive composition and signed correction.
The [separate degree certificate](u15_packed_exact_degree1936.md) proves exact
1936 without altering this frozen compiler's upper-bound metadata.
