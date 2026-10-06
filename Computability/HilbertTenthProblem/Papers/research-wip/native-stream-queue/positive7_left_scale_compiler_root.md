# Complete repeated-left and shared-scale positive7 compiler

For r>=1, the complete symbolic positive7 polynomial now costs

    (224+33r+gM(8+2r))M+(504+44r+gA(8+2r))A
      =728+77r+gM(8+2r)+gA(8+2r) operations.              (1)

It keeps96+6r positive witnesses,23 comparisons,6+18r fixed roles and the same ordinary positive input. Its certificate costs(201+33r+gM)M+(459+44r+gA)A. Here m=8+2r and ell=62+6r; gM=2d+e and gA=d+e are the unchanged paid geometric-extension costs: use seed6 or7 for leading binary110 or111 of m, otherwise seed2 for leading10; d remaining bits contain e ones. The exact r=0 fallback remains903 operations/96 witnesses. The actual numerical universal presentation and source degree remain open; general84 is unchanged.

The first original metadata-only emission has three complete graphs, r=1,2,4, totaling2,743 rows. This is a new complete source, not a lower count assigned to any frozen predecessor. The local proofs and independent full-source review remain separately identifiable evidence.

## 1. The two exact identities and their actual input interfaces

The [repeated high-left proof](positive7_left_pack_repetition_pascal.md) starts from the [complete repeated-pack parent](positive7_repeated_pack_compiler_root.md). In low-to-high order its high-left word has two copies of(H2,...,H7), two copies of(H1,...,H5,H7), four copies of(H1,...,H7), then two copies of each relator's(A1,A2), followed by S and D. The low selector prefix Q and its final join P^m*L+Q have already been shared and remain outside this high-word cut.

The parent's paid support supplies P2,P3,P6,P7 and Pm=P^m. Prepare new powers P4=P2^2, P5=P2*P3, P12=P6^2, P14=P7^2, P28=P14^2 and factors U4=1+P2,U6=1+P6,U7=1+P7,U14=1+P14,G7=U7*U14. These cost6M4A, including every support even if another computed power happens to agree for a particular r.

Compute the full seven-history Horner word B7 at6M6A, retaining its first intermediate K=H6+P*H7 and penultimate word B6a=H2+P*H3+...+P^5*H7. Then

    B6b=B7-P5*(K-H7)=H1+P*H2+...+P^4*H5+P^5*H7

costs1M2A beyond the paid support. Start acc=D*P+S, then descend through relators in reverse slot order using

    pair=P*A2+A1; repeated=U4*pair;
    acc=P4*acc+repeated.

Each relator quartet costs3M2A. Append the four seven-history blocks by acc=P28*acc+G7*B7, then the six-field pairs by acc=P12*acc+U6*B6b and acc=P12*acc+U6*B6a. These final three joins cost6M3A. Altogether the high word costs(20+3r)M+(16+2r)A, replacing(53+4r) of each operation.

For any finite block b of length n and high word a, two repeated copies give P^(2n)*a+(1+P^n)*b, and four copies give P^(4n)*a+(1+P^n+P^(2n)+P^(3n))*b. These polynomial identities, in exactly the stated descending order, prove equality of the high-left word. No positivity, selector exclusivity, division or native theorem is invoked. The possible negative subtraction used to form B6b is an exact polynomial identity, not a truncation of a packed integer.

The [shared native-power proof](review_positive7_shared_native_power_aristotle.md) uses the now paid P12, the retained P7 and the retained Pm. Since ell=3m+38, four products

    V=P12*P7; W=Pm*V; X=W*W; T=Pm*X                    (2)

give P^19,P^(m+19),P^(2m+38),P^(3m+38)=P^ell. These hold for all integer P, including0,1 and negative values. The old initial square P2 remains paid in the pack support; only the remaining pc(ell)-1 products are replaced. The native saving is therefore pc(ell)-5, at least2 for all r>=1. For68<=ell<128, floorlog ell=6 and popcount ell>=2; for ell>=128, floorlog ell>=7. No monotonicity of binary-power cost is assumed.

## 2. Exact complete splice and unchanged positive zero tuples

The sole source input is the committed repeated-pack receipt with SHA2562fd115c545d412be63b469023b8e13da68648dc79ead5086df2f0aaac6b6377a. It is parsed only as inert row/name/binding metadata. The new composer copies the entire prefix through the selector polynomial verbatim, including all forms, shared powers, geometric extension and Q.

It removes every old high-left shift/join and emits the complete schedule above. The old high-output Horner records remain literal. The old left high exit left_join_m is replaced only at left_selector_shift, while the packed_left exit name and every other left/right/output join remain unchanged. The old remaining native power rows are removed and the four products(2) are emitted after their actual Pm/P12/P7 producers. Their final native_shared_scale replaces the old scale exit only at pell_q=16*T. The parent scale_square_0 remains available to all old and new consumers.

Those are the only two executable external consumer substitutions. Every other retained record, including all native rows after pell_q, paired action, quotient append, positive lift, recurrence right sides and finalizer, stays literal. The old mask semantic_product lane descriptions and every lane meaning remain unchanged. No removed internal name may survive as a runtime input.

At the unchanged source cut, the high-left word and prescribed scale are equal polynomials for arbitrary signed integer assignments. Substitution into the same two consumer records therefore preserves every native residual and the entire final sum-of-squares polynomial on the identical supplied tuple. In particular the parent's positive guard/domain proof, simultaneous state/form carry recovery and positive completion transfer without a new existential map, weaker guard or witness restriction. Fixed coefficient correlations required by the actual-relator recipe remain exactly the parent's correlations.

The graph's ports.T names the new native scale; its high_left_pack and left_support_P12 ports expose already computed values. The obsolete binary power_cost field is replaced by native_scale_products=4 and a separately named parent_binary_power_cost for historical comparison. The old pack_splice receipt is superseded by an explicit left_scale_splice receipt binding this particular parent, removed rows and two rewritten consumers. These are metadata changes, not new witness or coefficient interfaces.

## 3. Disjoint all-r ledger and saved graphs

The three packs, their shared supports, unchanged geometric extension and low selector polynomial now cost(108+13r+gM)M+(91+10r+gA)A. This is also obtained by adding the retained right pack, new high-left word, retained high-output word and shared low-prefix work directly; it is not extrapolated from examples.

| Disjoint stage | M | A |
|---|---:|---:|
| Input, geometry, centers and guard without private masks | 8 | 134+12r |
| Centered form producers | 8r | 8r |
| Three packs and all geometric support | 108+13r+gM | 91+10r+gA |
| Shared prescribed native scale | 4 | 0 |
| Complete native certificate | 33 | 31 |
| Paired action | 30 | 168 |
| Selected centers and quotient appends | 12r | 14r |
| Fused positive lift | 12 | 21 |
| Recurrence right sides | 6 | 14 |
| Certificate | 201+33r+gM | 459+44r+gA |
| Residuals, squares and sum | 23 | 45 |

The deleted cuts have105+8r+pc(ell) rows. The two new schedules add40+5r rows, with the two consumer rows retained under substitution. The exact total saving is65+3r+pc(ell)=70+3r+pc(ell)-5.

| r | Deleted rows | New rows | Previous full M/A | New full M/A | Operations | Witnesses |
|---:|---:|---:|---:|---:|---:|---:|
|1|120|45|298/590|262/551|813|102|
|2|129|50|330/634|292/593|885|108|
|4|146|60|403/728|362/683|1045|120|

The first emission's operation-label census matches these handwritten counts, totaling2,743 saved rows and240 fewer rows than the parent examples. It has no additional formula-only cases. Every computed/supplied port is syntactically live, every operand topologically bound, the fixed-role set is unchanged, and all23 comparison pairs and68 finalizer rows are literal. These author self-checks are separate from the independent full-source audit.

## 4. Retained boundaries and evidence

**Remark1 (left repetition does not duplicate selected outputs).** Two equal left inputs may accompany different output lanes, such as0 and1, whose two-lane polynomial is P rather than the zero from repeating the first output. This is an arbitrary-integer local boundary, not a complete native zero. The high-output word is retained unchanged; no output equality or AND-linearity shortcut is used.

**Remark2 (support powers and shared square remain charged).** The new high-left stage pays all its support powers. The old P2 stays in the retained pack prefix, so the four-product scale saves pc-5 rather than treating that still-used square as deleted. Any further reuse of coincident powers needs an actual source/binding proof. Four scale products are a valid uniform schedule, not a minimum theorem.

**Open question3 (future form sharing and universal data).** Further sharing of common decoded histories or coincident powers is outside this source. The actual universal presentation and numerical relator list, the resulting numerical universal-equation bound, source degree and global arithmetic optimality remain open. Earlier local proofs' complete-composition obligations are addressed here only to the extent independently certified by the companion full-source review; their frozen historical scopes are unchanged.

Root authored the complete composition after reading the frozen local proofs. Aristotle independently derived the disjoint all-r count and exact source cut obligations; Riemann independently challenged both local proofs and the full expected cut/saving before emission. The new original metadata-only composer was read in full and ran once successfully. It is now frozen with its first receipt and must never be replayed/imported. No supplied, archived, committed, predecessor or frozen helper was run; no saved arithmetic source or coefficient array was evaluated or degree-propagated; no scientific sampling or build was used.

Frozen positive7_left_scale_compiler_root.py SHA256: 953acfebb2a6772e6dad3dcd8ea68f1fb83de1a2978593ed7eadceb28ee35d99.

Frozen positive7_left_scale_compiler_root.json SHA256: 9a17d38559ae0fc1aac7c987fab827120cdda346fdf2b85fe1b0eb9b1b523d4a.
