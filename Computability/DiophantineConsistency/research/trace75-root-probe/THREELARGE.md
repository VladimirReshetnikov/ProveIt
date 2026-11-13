# Excluding main index three when the first index is at least three

`Trace75ThreeLarge.impossible` is a generic model arithmetic theorem. In any
`IΣ₁` model, given `2≤X`, `2≤Y`, `0<eta`, `3≤n`, it shows that these two
explicit equations cannot both hold:

```
2*ycoord n (2*(X*Y²-1)+1) = k,
k*Y+eta = ycoord 3 ((X*Y+Y)-1).
```

The first is the trace75 first-ordinate equation, the second the main
ordinate at index three. The proof uses monotonicity and the exact third
ordinate to compare the two squares: for X,Y≥2, `X*Y²≥X*Y+Y+1`, giving
`k+2≥2*(c+1)`, inconsistent with `c=kY+eta>k`. These are explicit generic
hypotheses; this module has not yet bound the inequalities and equations to an
actual graph zero. It says nothing about the first-index-two case. Thus it
does not establish the unconditional exclusion of main index three, a halt
equivalence, trace74 guards or an iPRA result.

Accepted `Trace75ThreeLarge.lean` SHA-256
`d6a674347349d34153df8467dce732cb94e8681dd788a9e59964e921dda30206`;
`run-threelarge-v5.py` accepted `observations/threelarge-attempt05/`, object
`/tmp/trace75-threelarge-rrvtuerc/Trace75ThreeLarge.olean` SHA-256
`d8e8d07e7b91ee60a8afe6ea393f839f9c49aa386185d134d2bdefee8ca7b604`.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]`. Earlier
four failed source snapshots and diagnostics are retained. The selected direct
arithmetic and tactic imports are pinned; project/package transitive,
historical source/object and dynamic ancestry remain inherited.
