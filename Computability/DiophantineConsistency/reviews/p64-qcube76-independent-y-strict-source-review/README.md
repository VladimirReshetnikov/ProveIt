# Source review of the independent-`y` strict guard draft

This read-only review inspected `IndependentYStrictDraft.lean` at SHA-256
`c959e856d4554e735c57ef91f9255633a5ff899639f0222a2e8a11a02e61ad2a`, together
with the stated generic-bound and actual-size draft interfaces. It found no
concrete mathematical defect in the proposed strict bound.

The local `cValue`, `aValue`, and `rankValue` definitions match, on source
inspection, the q-cube graph's carrier, base and rank expressions; the
`oldV` decomposition uses `V=f²*(c*T−R)−c`. The new graph's auxiliary
residual has the stated expression `A*(V²−y²)+y²`, with
`A=Delta*(f²−1)`. The proposed `actual_strict` supplies the generic lemma
with a positive new `y`, `c≥3`, the actual-zero bound `f²>c+1`, and `A≥2`.
The last inequality follows from `Delta≥2` and positive integral
`f²−1`. The generic strictness argument excludes its only relevant equality
case `V=y=1` via `f²>c+1`.

This is source-level mathematical and interface inspection only. The claimed
expression equalities, definitional reduction, simplifier/cast behavior,
model theorem imports, and tactic proofs have **not** been checked by Lean
in this review or in the draft. In particular, inspection does not establish
that the two independently written carrier/rank expressions elaborate as
definitionally equal, nor that the generated graph matches the external JSON.
The positive-zero witness maps and iPRA endpoint remain separate.
