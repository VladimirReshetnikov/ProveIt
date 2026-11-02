# Independent conditional rank-phase audit

The read-only [audit](audit.py) of `d6105f61f0` exited 0 in session 31218;
its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
bind the result. Both source/object hashes, recorded compiler and direct
package-import exits, and author wrapper session 74044 exit 0 were checked.
The 70-source comparator was rerun and exited 0. Both outputs match and the
three axiom reports per side contain only Lean metatheory `propext`,
`Classical.choice`, and `Quot.sound`, with no warning, error or `sorryAx`.
No Lean compilation was rerun. Foundation's unobserved outer-wrapper exit
and package-transitive/dynamic provenance remain inherited.

In an IΣ₁ model, the first theorem assumes modulus=4n and C mod modulus=1,
and obtains (C−1) mod 4=0 via an explicit quotient. It does not require a
positive-modulus premise; the modulus-zero case is compatible with the
model's modulo convention. The second assumes q mod 4=0, A mod 4=0,
M mod 4=3 and R=A+M+qD+q²E+q³H, concluding R mod 4=3. The third composes
them with A=C−1. The audit exercised 900 bounded standard cases including
modulus zero as sanity checks, not as the model proof.

The author reports an earlier exploratory exit 1 with `sorryAx` after an
incorrect rewrite and a corrected exploratory exit 0; full exploratory
transcripts are not separately retained. The current theorem does not derive
its origin, block identity or residues from an actual fixed-port zero, prove
a model converse or calibration, or produce an object-level iPRA proof.
