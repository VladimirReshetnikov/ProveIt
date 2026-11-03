# Trace75 main index three is impossible for beta at least two

`Trace75ThreeExcluded.main_three_impossible` is checked in every `IΣ₁` model.
For arbitrary natural ports satisfying `2≤beta` **in the model**, ten positive
witnesses and a zero of the Lean trace75 value in the model's difference
ring, it proves that the following two explicit equations cannot both hold,
for any model element n:

```
2*ycoord n (2*(X*Y²-1)+1) = k,
c = ycoord 3 (A-1),       A = X*Y+Y.
```

The proof combines the actual graph reduction to first index two, the exact
signed eta identity, and the generic ordered-ring gap. It proves X≥2 and
Y≥8 from actual positive graph witnesses, converts the strict gap back from the
difference ring, and obtains a contradiction from `q≥3`, `X=q*w`, and
`Y=q*(q²*s)`. Its `2≤beta` is explicit; the theorem is not stated for beta=1
and this packet does not discharge it for a particular symbolic fixed port.
It does not itself export an existential main-index bound, halting/iPRA
result, trace74 guard or Lean binding of JSON/payload bytes.

Accepted source `Trace75ThreeExcluded.lean` SHA-256
`80b330a40343af9c62b27c3c37fa1dbd12724e8b812770bfc654ce6fbf798598`;
`run-threeexcluded-v2.py` accepted `observations/threeexcluded-attempt02/`,
object `/tmp/trace75-threeexcluded-bprrnf0k/Trace75ThreeExcluded.olean`
SHA-256 `8846a1b0774206168399b693decd4ac80688271928caac534eb36dcf82b9794a`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
The first failed attempt and its source snapshot are retained. Selected
direct providers and nearby upstream objects are pinned; project and package
transitive, historical source/object and dynamic ancestry remain inherited.
No complete selected closure audit or independent replay is claimed.
