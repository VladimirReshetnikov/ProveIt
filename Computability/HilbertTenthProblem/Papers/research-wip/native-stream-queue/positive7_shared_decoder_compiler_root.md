# Complete positive7 compiler with shared history decoding

For r>=1 the complete symbolic positive7 polynomial now costs

    (224+30r+gM(8+2r))M+(509+41r+gA(8+2r))A
      =733+71r+gM(8+2r)+gA(8+2r) operations.             (1)

It has96+6r positive witnesses,23 comparisons and6+15r linked fixed roles. The certificate is(201+30r+gM)M+(464+41r+gA)A. Here m=8+2r, ell=62+6r and gM=2d+e,gA=d+e retain the already paid geometric-extension grammar: seed6/7 for leading110/111, otherwise seed2 on leading10, followed by d bits containing e ones. The same ordinary positive integer input and the r=0 fallback903/96 remain. A numerical universal relator presentation, source degree and global arithmetic optimality remain open; general84 is unchanged.

The replacement implements the [local shared-decoder proof](positive7_shared_form_decoder_pascal.md) inside the [complete repeated-left/shared-scale parent](positive7_left_scale_compiler_root.md). A canonical permitted fixed basis preparation makes every runtime wire uniform. Polynomial equality is for the same canonical fixed recipe in parent and child, not for unrelated assignments to their different coefficient-role interfaces.

## 1. Canonical fixed preparation and the exact producer identity

For a noncentral fixed relator P=[p,q;s,t] in SL2(Z), divide w0=(2q,p-t,-2s) by its positive coordinate gcd to obtain primitive w. Let k be the first nonzero original coordinate. Apply only the transposition(1,k), and in that coordinate order prepare

    g=gcd(w1,w2)>0, a*w1+b*w2=g,
    u=(w2/g,-w1/g,0), v=(-w3*a,-w3*b,g).

Undo the same transposition in both rows. The original-order u has third coordinate0: for k=1 this is the displayed formula; for k=2 it becomes(-sign(w2),0,0); for k=3 it becomes(0,-sign(w3),0). For P=+/-I keep u=e1,v=e2,Eplus=0,T=I2 and the inherited central section; no zero invariant is normalized. This choice is a permitted specialization of the parent's preparation for every fixed P, not a runtime basis change.

Use the SAME V=[u;v] for the parent and successor. With

    C=[1,0,0,-1;1,1,0,-2;2,0,1,-4], h=(H4,H5,H6,H7)^T,

prepare ell=V*C, Eplus with S(P)-I=Eplus*V, the inherited section J0 with V*J0=I2 and T=V*S(P inverse)*J0. The section uses c*w=1 for the original-order primitive w, after undoing the preparatory transposition, and J0 is the first two columns of [u;v;c] inverse. Every action coefficient, including Eminus=-Eplus*T in the parent derivation, remains tied to this V. No numerical relator coefficient array is evaluated by this composition.

The common center W=lambda*D*J is already paid outside the form cut. The old producer outputs are A1=ell_1*h+W and A2=ell_2*h+W, at8M8A per relator. Compute once

    c1=H4-H7; k=c1-H7; c2=k+H5; k2=k+k; c3=k2+H6.        (2)

These five additions/subtractions give(c1,c2,c3)^T=C*h exactly. For each relator compute

    A1=(u1*c1+u2*c2)+W,
    A2=((v1*c1+v2*c2)+v3*c3)+W.                         (3)

All five fixed products and all five additions are paid, even when their coefficients are0 or1. Since u3=0, equations(2)-(3) are exactly the old two polynomials for every integer assignment to the runtime histories and W. Signed decoded words are computed intermediates, not positive witnesses or new native lanes. In the central case the same template explicitly retains the zero products.

## 2. Guard and same-tuple polynomial preservation

The guard constants still come from the four-coordinate ell rows, using

    b*C=(b1+b2+2b3,b2,b3,-b1-2b2-4b3),
    lambda=1+max(0,all -ell entries), Cg=2lambda+1,
    pplus=max(0,all ell entries),
    K dyadic >max(Cmass,m,Cg,lambda+pplus).               (4)

These fixed integers may be prepared offline even though the eight ell entries no longer occupy runtime coefficient-product roles. The global guard Cg*(D*J-S)=Ztot+g, its producer, center W and all selected-center recovery remain literal. The native theorem consumes A1,A2, which agree with the parent. It does not require positivity of c1,c2,c3.

Thus the prior proof of positive native input forms before projection, simultaneous state/form carry recovery, quotient action and positive completion transfers on the same supplied tuple. More directly, all changed form exits are equal integer polynomials and every consumer outside their producer cut is unchanged. Substitution proves equality of the entire final polynomial under the linked canonical fixed recipes, including every residual before the sum of squares. This also proves equality of the positive zero tuples and ordinary-input projections. It is not a comparison between arbitrary independent old and new fixed coefficient values or a parent prepared using a different V.

## 3. Complete source cut and fixed-role binding

The sole source input is the committed parent receipt9a17d38559ae0fc1aac7c987fab827120cdda346fdf2b85fe1b0eb9b1b523d4a. Its rows are parsed only as inert records. Replace exactly the old shared_centered_input_forms stage, containing16r rows, by the five shared decoder records and10r sparse-form records. The exits centered_form_j_1 and centered_form_j_2 keep their original names. All outside prefix and suffix records stay literal; no external arithmetic consumer is rebound.

Retire exactly the8r form_ell roles and introduce exactly5r original-order form_basis_u/v roles. The remaining6 global roles,6r Eplus roles and4r quotient_T roles are unchanged, giving6+15r in total. Their actual fixed values still obey the canonical preparation above and(4). The role count is a count of syntactic fixed roles, not independent mathematical parameters. Each role occurs in one paid multiplication.

The old left_scale_splice metadata is replaced by this transformation's form_decoder_splice, recording every removed/new row, unchanged exit, complete external-consumer list, old/new source digests and role changes. Existing lane descriptions, comparison pairs, positive auxiliary names and every old computed port are unchanged. The new decoded_history_fields port names only the three already computed decoder values. The four-product native scale and its current cost4 remain unchanged. No old source audit is relabelled as an audit of this successor.

## 4. Disjoint all-r ledger and complete examples

| Disjoint stage | M | A |
|---|---:|---:|
| Input, geometry, centers and guard | 8 | 134+12r |
| Shared history decoder | 0 | 5 |
| Sparse centered forms | 5r | 5r |
| Three packs and all geometric support | 108+13r+gM | 91+10r+gA |
| Shared native scale | 4 | 0 |
| Complete native certificate | 33 | 31 |
| Paired action | 30 | 168 |
| Selected centers and quotient appends | 12r | 14r |
| Fused positive lift | 12 | 21 |
| Recurrence right sides | 6 | 14 |
| Certificate | 201+30r+gM | 464+41r+gA |
| Residuals, squares and sum | 23 | 45 |

This independently sums to(1). Relative to the exact parent the difference is3rM+(3r-5)A, or6r-5 operations. At r=1 it saves three multiplications while adding two additions, a one-operation total improvement.

| r | Literal outside cut | Removed rows | New cut rows | Certificate M/A | Full M/A | Operations | Witnesses | Fixed roles |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|1|797|16|15|236/508|259/553|812|102|21|
|2|853|32|25|263/547|286/592|878|108|36|
|4|981|64|45|327/631|350/676|1026|120|66|

The three complete graphs have2,716 rows:2,631 literal outside rows and85 new cut rows, versus112 old cut rows. No unchanged outside row is rebound. The14 original form-exit names are reused within the85-row replacement; the row partition is by the declared producer cut, not by disjoint old/new name sets. All23 comparison pairs and68 finalizer rows remain literal. The composer checks every operand binding, unique name, supplied/computed liveness, role occurrence, old/new stage census, outside equality and cut fanout without evaluating arithmetic instructions.

## 5. Retained boundaries and evidence scope

**Remark1 (valid six-addition alternative).** Root's earlier decoder w=H7+H7,k=H4-w,c1=k+H7,c2=k+H5,k2=k+k,c3=k2+H6 remains a valid6A schedule, saving6r-6. Computing c1 first as in(2) saves one shared addition. The earlier schedule was not false.

**Remark2 (sparse coefficients do not supply the guard bound).** For central u=e1,v=e2, all five sparse coefficients are0 or1. Substituting their negative maximum would choose lambda1/Cg3, but ell_2=(1,1,0,-2). With H1=...=H6=1,H7=10,D=17,J=1,Ztot=0,g=3, the altered guard3*(17-16)=0+3 holds while A2=1+1-20+17=-1. This is a local guard/producer counterexample, not a complete native zero. The actual ell-based lambda is3, and the unchanged recipe(4) is required.

**Remark3 (same canonical recipe is essential).** The displayed fixed-wire schedule requires u3=0, proved for the chosen transposition recipe. It is not justified by sparsity alone after an arbitrary unrecorded permutation. The local proof supports arbitrary fixed permutations by statically choosing different decoded wires; this complete source deliberately uses the explicitly canonical option throughout the parent/child comparison.

**Open question1 (remaining sharing and numerical frontier, credited to root).** The preceding local proof's complete-source obligation is addressed by this particular emission and companion independent audit, leaving its frozen historical scope unchanged. Power/factor alias savings and other arithmetic changes need their own complete source and consumer proof. Numerical universal relators and their resulting equation bound, degree and optimality remain open; no generic lower bound for5A or5M5A is asserted.

Root wrote a fresh original metadata-only composer after the local proof and independent count challenge. The full source is a finite inert instruction description; no saved instruction or coefficient array was numerically or symbolically evaluated, and no degree was propagated. The full composer was read before its sole successful run and is now frozen with its first receipt. Pascal independently read its entire pre-emission source and passed the cut/recipe challenge; his optional original-order section wording was clarified before the run. No supplied, archived, committed, predecessor or frozen scientific helper is executed/imported. No scientific sampling or build is used. Independent reviews must bind this exact new trio; author metadata checks alone are not the independent audit.

Frozen positive7_shared_decoder_compiler_root.py SHA256: bb333134e85cc6ca8ce11a1469d5c4b0ca95357551f295e7a4bb885ed2319b8f.

Frozen positive7_shared_decoder_compiler_root.json SHA256: e6539f0c8b8d66b53537d228425932a0a3d030e78d5f96be0d68d513ebe20b95.
