# First-Pell seed offset divisible by XY

`Trace75SeedOffset.offset_divisible` is Lean checked in every IΣ₁ model.
For X,Y>0 and arbitrary natural r it proves there is a natural ρ with

```
2*ycoord (r+1) (2*(X*Y*Y-1)+1) = (2*r+1)+1+(X*Y)*ρ.
```

The proof uses the represented Pell residue quotient and chooses
`ρ=4*Y*s`. It assumes no graph zero or rank equality and does not establish
halt, iPRA or file binding. Accepted author check
`observations/offset-attempt01/` produced
`/tmp/trace75-seedoffset-8whskqn1/Trace75SeedOffset.olean` SHA-256
`3ebcc03a5d12f348c46d5d79f6ce499f4f14f80f1d23e011e3c18f3707567d9c`.
Direct providers were pinned; transitive, package and dynamic ancestry remain
inherited.
