# Independent source review: two-sevenths index separation

The reviewed source SHA-256 is
`3ecd08615e90b699f91c23ec2bf9085a05bb14599731fc8f68646bd1505b6ef4`.
The threshold calculation is correct. Given `w≥2`, `7w≤2n`,
`18w+10≤B`, and `D=3n−10w`, the first two assumptions imply
`3w+1≤n` and `D≥0`. If `L=2w(n+w)+5w`, the identity

```text
(36w+20)D−2L = (2n−7w)(52w+30) ≥ 0
```

and `36w+20≤2B` imply `L≤BD`. The proof justifies model truncated
subtraction before reasoning in the difference ring.

For `n≥7`, the model quotient `floor(2n/7)` is at least two: otherwise
the division algorithm and remainder bound give `2n≤13`, contrary to
`2n≥14`. Choosing `w=min(floor(2n/7),32781)` gives `7w≤2n` and
`18w+10≤67·8807=590069`, since `18·32781+10=590068`. The client
therefore establishes `n+min(floor(2n/7),32781)<r` for the supplied
same-zero ordinates without an upper bound on `n`. The existential theorem
retains the earlier quarter-width bound with cap 118013 for the very same
pair, as well as the linked ordinates, residue, oddness and earlier bounds.

This is an independent source-level arithmetic and interface review, not
an independent Lean replay or a transitive provider/package audit. The
result does not establish the reverse guard, eliminate all zeros, bind
symbolic ports to the external payload, or provide an iPRA endpoint.
