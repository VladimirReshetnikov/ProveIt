# Specializing the public variables of K without changing consistency strength

## Precise separation from membership vacuity

The native bundle combines full atomic membership vacuity V(a,b,c) with the seed-K schema. V must remain arbitrary in its public labels: it is needed by the inherited first-order bootstrap. The specializations here change only the seed-K part. The original gate c != a,b remains and disabled instances still output truth.

Let Phi_c be the decoded matrix with native code c. In the ordinary seed-K schema let p be the input variable, y the output variable, and z the private container variable. Denote the full support-bearing seed formula by K(p,y,z;Phi_c).

Consider the following replacement of the enabled bundle:

V(a,b,c) AND K(0,1,c+2;Phi_c).

Every other logical row and proof rule is unchanged.

## The fixed-public-variable theorem

This modified native calculus is equiconsistent with the predecessor's K calculus, and hence with ZFC, by finite proof translations formalizable in ZFC.

For the upper translation, every label occurring in Phi_c is strictly less than c (with c=0 interpreted as truth). Thus c+2 is absent from the matrix and differs from both 0 and 1. The second conjunct is a legitimate ordinary K instance, while the first is legitimate vacuity by the unchanged gate. Here "ordinary K instance" refers to the inherited first-order interpretation: it is not asserted to be literally one of the predecessor's native rows, whose private variable equals its matrix code. All retained logical rows are unchanged.

For the lower translation, every legal vacuity instance is still obtained by projection from an enabled bundle. Hence the inherited bootstrap to ordinary first-order logic with equality is still available. Consider an arbitrary ordinary K schema instance with an input variable, an output variable, a finite tuple of parameters, and a fresh private variable. First take its universal closure. Rename bound variables capture-avoidably so that its public input/output roles are 0 and 1, and every independent parameter has a different label. The private variable is chosen after encoding this renamed matrix, as c+2. The emitted instance and its universal closure (obtained by generalization) are alpha-equivalent to the desired closed instance. Alpha conversion has a primitive recursive first-order proof transformation. This applies to every axiom occurrence in a finite derivation.

Independent parameters initially named 0 or 1 are not lost: they are renamed simultaneously to fresh labels before the public roles are assigned 0 and 1. The existence of infinitely many variable labels supplies these names. The argument does not silently permit a parameter to coincide with the distinguished input/output role.

The original gate does not prevent coverage. For any matrix code c, choose the emitter's unrelated a,b to differ from c. These fields now control only the vacuity conjunct, so some enabled batch emits the required K instance. For the lower consistency calibration, ordinary K with distinct input/output roles is sufficient. Coincident-role native instances are not being claimed alpha-equivalent to the fixed distinct labels 0 and 1.

## One fixed public variable with no new private arithmetic

There is another safe family closer to the original source. Fix only the K input variable to label 1 and leave its output label b arbitrary, retaining private variable c:

V(a,b,c) AND K(1,b,c;Phi_c).

The original gate ensures c != b. If c != 1, the private variable is fresh from both public variables and the matrix. If c=1, the matrix is native falsum; under the inherited irreflexive-membership interpretation it is identically false even under variable capture. For a false matrix the witness-request condition is true and the support condition is met by an empty container. Thus the exceptional collision is harmless for the upper consistency translation. The allowed coincidence b=1 is the same empty/singleton public-variable coincidence already covered in the parent calibration.

For the lower direction, choose ordinary variable names so that the K input is 1 and all other distinguished names avoid it. Formula padding by double negation supplies arbitrarily large codes for an equivalent matrix, so exceptional code collisions can be avoided. The full vacuity bootstrap is still untouched. Fixing the output instead of the input is equally sound.

One can similarly use the two fixed public labels 1 and 8 while retaining private label c. The native constructors give 8=I(0,1), so both codes 1 and 8 decode as false under the irreflexive interpretation. The only possible private/public collisions are therefore false-matrix cases. This does not assert that the native calculus proves its own falsum is false; it is a statement about the upper interpretation used for consistency calibration.

## A predecessor private label

For every native code n>=2, every variable label in its decoding is at most n-2. For relation/equality fields this follows from P(x,y)>=max(x,y), since n=4P(x,y)+tag. For implication and quantification, apply the same field bound and induction on proper matrix subcodes. Codes 2 and 3 use only label 0.

Consequently a seed with matrix Phi_(c+1) can use c as its fresh private variable whenever c>=1. If one K public variable is fixed to 0, the only collision with the private variable is c=0, whose matrix is code 1, again false. The other public variable remains protected by the unchanged gate. Nonzero matrix codes suffice for lower schema coverage after double-negation padding. This yields another safe formalism, although the measured source did not improve the state count.

## Measured implementation outcome

These are logical reductions, not achieved machine improvements. Measurements used the exact K220 source with 208 DAG nodes and 4,744 primitive occurrences, then performed complete guarded graph checks of the resulting source.

- Fixing both public variables to 0,1 and private c+2 gave 218 source DAG nodes, with 4,683 occurrences (4,677 after swapping input/output constants).
- Fixing public variables to 1,8 with private c gave 217 DAG nodes with a balanced constant-eight emitter.
- Fixing one public variable to 1 gave 212 DAG nodes. The input-fixed source compiled provisionally to 224 states; no full runtime proof was claimed.
- The predecessor-private-label family gave 214 or 215 DAG nodes; its one provisionally compiled table had 228 states.
- A further 800 seeded closed-atom grammar parses did not improve these direct source counts.

The source DAG and provisional state counts do not prove runtime correctness. The full positive theorem concerns the presented calculi. These implementations demonstrate that a logical specialization can reduce primitive occurrences while making the shared decoder larger.
