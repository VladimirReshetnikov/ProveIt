# Multiplication equations in the candidate PRA theory

`PRAMultiplication` proves actual Foundation derivability statements for the
candidate theory: `PRA ⊢ mulZeroSentence` expresses `x·0=0`, and
`PRA ⊢ mulSuccSentence` expresses `x·succ(y)=(x·y)+x`. The sentences use the
designated primitive-recursive multiplication, addition, zero and successor
codes and bind all variables. The proofs derive the equations from the
composition, projection, zero and recursion defining equations in every
equality model of the candidate theory, then apply Foundation completeness.
They do not infer object-theory provability from standard-Nat truth.

The final main source and focused checks compiled with Lean 4.32 using
`-M6000 -j1 -DElab.async=false` in `/tmp/pra-multiplication-author-k_2dtgvm/lib`.
The final main log is empty and all eight axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The sole direct prerequisite is the
merged `PRAAddOne` client; its provider is inherited through the private
addition overlay from `/tmp/pra-merged-clients-k8u39e5a/lib`. Foundation and
Mathlib remain the inherited boundaries. Independent review and replay of this
pair are separate.

Four main snapshots/logs and two checks logs are preserved in the private
`logs` directory. The first main attempt had a misdirected rewrite; attempts
2 and 3 passed. Attempt 4 removed an unnecessary `PRAAddition` import and
passed; the checks' complete logs and object match across both versions.
No multiplication attempt used `sorry`. These equations advance compatibility
but do not yet prove equivalence with a standard PRA presentation, IΣ₁
conservation, or the Diophantine consistency equivalence in PRA.
