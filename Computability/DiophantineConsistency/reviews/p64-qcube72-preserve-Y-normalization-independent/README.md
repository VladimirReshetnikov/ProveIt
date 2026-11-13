# Independent review: conditional preserving-Y obstruction

**PASS as a standard-integer conditional deduction.** At the fixed beta and
masks, suppose an actual positive 72 zero has positive `s` cube-free,
`1≤J≤beta+1`, and `J≡2 (mod 3)`. Then beta is 1 modulo 3, so
`q=beta*J+1` is divisible by 3. If an actual positive 76Y zero at the same
ports had the same Y, with `q'=beta*J'+1` and positive `s'`, then
`q'³s'=q³s`. For every prime p, cube-freeness bounds `v_p(s)≤2`;
therefore `3v_p(q')≤3v_p(q)+v_p(s)` implies `v_p(q')≤v_p(q)`,
and hence `q'|q`.

Writing `q=q'd`, both q and q' are 1 modulo the positive beta, so d is
also 1 modulo beta. If q' is a proper divisor, positivity of J' gives
`q'≥beta+1`, while `d>1` and the congruence give `d≥beta+1`.
Thus `q≥(beta+1)²`. But the stated J bound gives
`q≤beta*(beta+1)+1<(beta+1)²`, a contradiction. Hence `q'=q`,
contradicting the checked 76Y no-three-divisor theorem, independently
reviewed [here](../p64-qcube76y-fixed-q-not-three-independent/README.md).
No target coordinates besides the derived q' and Y need be fixed.

The non-cube-free swap in the construction is valid as a **factorization**
example: for `J=2`, `q=2beta+1`, `q'=beta+1`, `s=q'³` and
`s'=q³`, both products equal `q³q'³` although q differs from q'. It is
not a graph-zero construction. The J bound is also sharp for the factorization
argument: with `J=beta+2`, `s=1`, `q=(beta+1)²`, `q'=beta+1` and
`s'=(beta+1)³`, equal Y allows a proper q' divisor. This last observation
alone says nothing about the mod-3 premise or graph zeros.

The construction's checker reran exit 0 and its output was byte-identical
to its pinned result. An independent [checker](check.py) used prime-factor
valuations on additional finite candidates, checked the sharp-J examples,
and verified the final source pins; its exit-0 output is [result.json](result.json).
Finite controls are not the proof above. The deduction assumes the source
zero and its restrictions; it does not produce one, rule out changing Y,
prove failure of existential equivalence, or establish the general argument
inside an IΣ₁ model. No Lean replay was performed.

Construction SHA-256: README
`656b2d4103ea05a1811e611f857ff6029cb2cf94bac7a450d627ac8591450739`,
checker `f028a28b63bcbca614d730fe46b30a44dc29f5cf7bfafa6fb5af6da5ee059e09`,
result `e41d17b44f86a6549a248f71b0dbab8e3c118650db26f0b54253801fce18df25`.
Independent checker SHA-256
`9ce1e24192aa9c57ce61f13afef0f09e2d72f6d7047ee19ab2698f3fb7d21593`;
result SHA-256
`73e4d08080e9fa97c30c238259807033623c934f7e08a7fc6726c5822e5aaca9`.
