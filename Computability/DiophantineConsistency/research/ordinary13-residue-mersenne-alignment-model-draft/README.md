# Conditional factor-three cancellation and radix alignment

This unelaborated fact-level draft applies the existing IΣ₁ source theorem
`ArithmeticAdaptiveMersenne2011.cancel_three` only after independently
obtaining `X=2^R`, `q∣3X`, `d≥4` and the represented model-natural equation
`q=(2^d-1)*J+1`. It therefore proposes `q∣X` **under those explicit extra
hypotheses**, not in the general residue projection problem. It supplies no
unproved Bézout premise. The imported theorem itself derives the relevant
arithmetic for this special form, conditional on its own provider chain.

For `J>0`, the separate `ArithmeticRadixAlignment.factor_alignment` source
then proposes a positive model N with `q=2^(d*N)` and an aligned quotient.
The actual graph, fixed compact port representation and exponent d,
port-to-model casts, predecessor growth and power-recovery clients, and all
Lean/provider/axiom checking remain open. No eta-zero or iPRA endpoint claim
is made. This packet does not invoke a free-J graph-zero theorem.

Run the deterministic static check with `python3 -I -S -B
research/ordinary13-residue-mersenne-alignment-model-draft/check.py`. It does
not execute Lean or establish elaboration.
