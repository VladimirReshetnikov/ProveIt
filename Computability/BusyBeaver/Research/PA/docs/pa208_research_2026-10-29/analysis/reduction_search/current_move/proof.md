# Moving the successful MP target directly into the current register

Replace the closed success body [3847,3873) by

`(CD4,(CI1,CC2))`.

The preceding exact comparison code enters this body only after checking
I(t,z)=h, with T=H=X=Y=0 and D=z. The loop transfers D into T, clearing D;
ordinary induction on z proves termination and the postcondition. Thus the
successful command result is `(z,w,0,0)`. Failure remains `(0,w,z,0)`.

Soundness is immediate from the unchanged comparison: the current theorem t
and cached theorem I(t,z) justify z. No arbitrary stack value is introduced.
The original conservative weight zero for MP remains valid.

Use the final source's three-command compiler, with S, MP, and AX. All its
helper uses of MP are forced failures, except the deliberately omitted J(0).
The helpers PUSH, DISCARD, H, and J(u>0) consequently retain their contracts.
For a proof of Y from A and M=I(A,Y), use

`B_M; PUSH; B_A; PUSH; S; S; MP(Y)`.

By the strong induction hypotheses, the tuple before the final MP is
`(A,w,0,M)`, unless an earlier command already halts. The successful MP now
returns `(Y,w,0,0)` directly; no cleanup block or reserved zero is necessary.
All other proof-rule compiler blocks are unchanged, so the strong theorem
holds for arbitrary initial top and stack with counter/cache zero. B_1;H
still halts. The unchanged AX reset prefix supplies cofinally many successful
candidate indices, and the scheduler still drains every unsuccessful
candidate.

The protected bootstrap suffix and conservative S/MP/AX credit proof are
unchanged. This is therefore an ordinary source-level calibration argument
for the same numerical calculus and Theory U. It does not supply a literal
binary-machine runtime theorem. The new source has 3,886 primitives and 198
DAG nodes; those numbers do not imply a state saving.
