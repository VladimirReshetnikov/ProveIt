# Independent source review: sharper minimum-width bound

The reviewed Lean source has SHA-256
`8c74879e5b76c45e668742114b8395b99699f6163eb0a76a01003d6c8ae2b10e`.
Its model-level threshold arithmetic is correct. With `D=3n−10w` and
`L=2w(n+w)+5w`, `w≥1` and `4w≤n` imply `D≥0`, `3w+1≤n`, and

```text
(10w+5)D−2L = (n−4w)(26w+15) ≥ 0.
```

If `5w+3≤B`, then `10w+5≤2B`; multiplication by nonnegative `D` and
the displayed identity give `L≤BD`. The source establishes the needed
truncated-subtraction identity before transferring it to the difference
ring.

For the fixed symbolic first port, `B=67·8807=590069`, and the choice
`w=min(n/4,118013)` is positive when `n≥4`, has `4w≤n`, and satisfies
`5w+3≤B`, since `5·118013+3=590068`. Thus the same supplied positive
graph-zero tuple and its ordinate indices satisfy
`n+min(n/4,118013)<r` without an upper bound on `n`. The existential
client preserves one linked pair, both ordinate identities, the
first-index residue, oddness, and the earlier `n+3<r<2n` bounds.

This is a source-level mathematical review and interface check, not an
independent Lean replay or a full transitive provider/package audit. The
result does not establish the reverse guard, eliminate all zeros, bind the
symbolic port to the external payload, or provide an iPRA endpoint.
