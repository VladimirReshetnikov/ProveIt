# Conditional positive 84/85 model comparison — source draft

This is an **unelaborated source-only proposal**. It imports the separate
uncompiled `RingComparison` and graph drafts through a prospective local
provider overlay. No Lean build, model theorem, provider compatibility,
iPRA endpoint, physical-file or PDF correspondence follows from this packet.

For a model `V` of IΣ₁, positive fourteen-slot valuation `v`, integer ports
`p` with `(p 0 : DiffRing V) = ι beta`, and `q = 1 + v 0 * beta`, the proposed
forward map changes slot 6 from `w` to `q*w` and slot 12 from `gamma` to
`gamma-w`. It explicitly requires `w < gamma`; the subtraction is natural,
so `P72Root.ι_tsub` is used only under that bound. The proposed reverse map
requires the explicit premise `q ∣ X`, writes `X=q*w`, and changes slot 6
to `w` and slot 12 to `gamma+w`. Since the original `X` is positive, this
quotient is positive. Remaining slots are unchanged. Both maps use the
separately drafted ring output identity, with no premise that the other graph
already has a zero.

The two model-zero implications in this file retain these extra premises.
In particular, this is **not** an unconditional 84↔85 equivalence. Closing it
requires extracting the signed graph field equalities and natural main/Pell
balances from each graph zero, validating the model order/sign and port casts,
then proving `gamma > w` for the 84 zero and `q ∣ X` for the 85 zero. The
reviewed modified-carrier gamma and Mersenne fact drafts give conditional
interfaces toward those facts; they do not themselves discharge the graph
hypotheses. Compact port identification, compatible compiled ancestry and the
upstream iPRA endpoint are additional obligations.

Run `python3 -I -S -B check_source.py` from any directory to replay the
ring-client observation and check 200 positive finite examples in each
direction, a strict-subtraction boundary and a nondivisibility control. These
are external finite controls and source inventory, not proofs of the arbitrary
model statements or of Lean elaboration. The exact assumptions and all imports,
rewrites, tactics and coercions require independent source review and a future
guarded Lean build.

Independent source review is recorded in
`../../reviews/ordinary14-84-85-conditional-model-draft-independent/`.
