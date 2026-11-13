# 85→86 q-cubed ring-field identity — source draft

This unelaborated source proposal maps 85 slot 7 `s` to 86 `Y=q³*s` and
slot 8 `r` to `r+s`. It proposes equality of all five residual evaluations
and the complete output over an arbitrary commutative ring. The first-root
cut uses `M=q³*b`: `M*(P−(r+s))+Y*b=M*(P−r)`. This is only a ring identity;
positive-model casts, witness updates and reverse quotient extraction are
separate.

The checker pins both candidate graphs, verifies the exact row delta, replays
their source generators and checks 300 signed finite assignments. It does not
run Lean or establish arbitrary-model elaboration. Provider ancestry, iPRA
endpoint, external files and PDF semantics remain separate.

Independent source review is recorded in
`../../reviews/ordinary14-85-86-ring-client-draft-independent/`.
