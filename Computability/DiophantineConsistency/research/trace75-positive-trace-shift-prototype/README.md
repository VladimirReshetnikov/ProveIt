# Positive squared-to-linear trace shift

`Trace75PositiveTraceShift.positive_shift` is Lean checked in any strictly
linearly ordered commutative ring. If `c>0`, `f>0`, `r≥0`, `f=1+c*d`, and
the old auxiliary value `f*f*(c*T-r)-c` is positive, then

```
Tnew = f*T-d*r > 0
f*(c*Tnew-r)-c = f*f*(c*T-r)-c.
```

This generic algebra does not itself construct a model-natural witness Tnew,
bind any trace75 graph, or prove a halt/iPRA result. The accepted author run
is `observations/shift-attempt02/`, object
`/tmp/trace75-positiveshift-y7sk8val/Trace75PositiveTraceShift.olean` SHA-256
`f37bfe2a63967448298d15fc8aac2da4ad491489453be6bcd9d73ebda8a94c7b`.
Attempt01 failed on the order of factors in a positivity lemma; its diagnostics
and source are retained. The accepted runner pins its direct Mathlib imports;
full transitive, package and dynamic ancestry remain inherited.
An independent source and receipt audit passed; no Lean replay was performed.
