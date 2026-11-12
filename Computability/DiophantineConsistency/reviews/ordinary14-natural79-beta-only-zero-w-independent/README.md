# Independent review: beta-only natural-79 zero-w draft

The [beta-only source proposal](../../research/ordinary14-natural79-beta-only-zero-w-draft/README.md)
and this independent checker reproduce. The reviewed changes have the stated
source interfaces and the mathematical size argument also covers `q=1`. No
concrete mathematical or source-interface defect was found in this bounded
review. This is not Lean elaboration, proof or provider verification.

The literal graph and its duplicate atom cut have identical checked source
prefixes defining `q = 1 + J*beta`, `X = q*w`, `Y = q³*(s+1)`, `U = Y*q²`,
and `a = X*Y+Y`; at `w=0`, `a=Y`. For a model-natural represented beta and
model-natural coordinates, `q≥1`, `Y≥q³` and `U>0` hold even when beta or J is
zero. In particular at `q=1`, `Y≥1`, so `0<3<4Y+3`. The source client passes
only the beta representation, zero and zero-w hypotheses to its signed
root/divisibility argument; it does not assume represented K0/MC/MF or positive
beta/J. The existing zero-w concrete unit extractor is explicitly quantified
over arbitrary four integer ports and has no representation hypothesis.

The signed magnitude source retains both possible signs; the scaled-quotient
source explicitly needs a positive scale, supplied by the new scale lemma.
Given their stated conclusions and the zero-w root cut, the first ring identity
proposes `H ∣ U`; substituting `H=4Y+3` and `U=Yq²` gives `H ∣ 3q²`. The
checker independently expands the two displayed free-ring identities. For
`q≥1`, `q²≤q³≤Y` gives `0<3q²<4Y+3`; the proposed signed-to-natural reflection
and internal positive-divisor bound supply the contradiction. These arguments
depend on the unelaborated model, unit, graph-binding and reflection lemmas;
polynomial identities do not verify those lemmas or Lean tactics.

[exact-deltas.diff](exact-deltas.diff) records **all** changes across the four
pinned original/alternative pairs. The checker reconstructs it and verifies
all source hashes; it independently verifies that the new pair-unit evaluator
copies the earlier J-positive helper verbatim. The endpoint removes its local
beta-positivity and K0-representation arguments but still imports the 80
endpoint and `StrictK0Symbolic`; their obligations are not discharged or
removed by this beta-only step. The alternative modules reuse names and must
be selected as alternatives in any future reviewed overlay.

The proposed source and all its dependencies, name and instance resolution,
full import/provider closure, and axiom reports remain unverified by Lean here.
No physical Carrier65 coefficient or PDF binding follows from this review.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-natural79-beta-only-zero-w-draft/check_source.py | cmp - Computability/DiophantineConsistency/research/ordinary14-natural79-beta-only-zero-w-draft/receipt.json
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-beta-only-zero-w-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-beta-only-zero-w-independent/result.json
```
