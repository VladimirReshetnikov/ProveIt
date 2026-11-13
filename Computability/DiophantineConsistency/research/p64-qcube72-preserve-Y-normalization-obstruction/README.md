# Conditional obstruction to preserving Y when normalizing to 76Y

Suppose there is an actual positive 72-graph zero at the fixed compact44 beta
and masks, with arbitrary K, satisfying

```
1≤J≤beta+1,  J≡2 (mod 3),  s is cube-free.
```

Then no positive 76Y-graph zero at the **same ports** can preserve the
resulting value `Y`. Here cube-free means that no prime cube divides the
positive integer s; the case `J=2,s=1` is included. This is a
standard-integer conditional deduction; no such 72 zero is known to exist.
It does not exclude an alternative 76Y witness with a different Y or prove
failure of existential equivalence.

## Why a 76Y zero has 3∤q

The checked [fixed-port 76Y theorem](../p64-qcube76y-fixed-q-not-three-draft/README.md)
proves in every IΣ₁ model that an actual positive 76Y zero has `3∤q`.
Its proof reconstructs the checked 76Y-to-72 witness update at coordinate 13,
retains q,Y,k,R, and derives its exact same-coordinate old-carrier identity.
The checked fixed-compact no-gamma theorem supplies the contradiction when
`3|q`. The Lean theorem makes no 72-zero existence claim.

## Rigidity of the Y coordinate

Let `beta=2^590069−1`, `q=beta*J+1`, and `Y=q³s`. Since
`beta≡1 (mod 3)` and `J≡2 (mod 3)`, the source q is divisible by 3.
For a positive 76Y candidate at the same ports, write `q'=beta*J'+1` with
`J'≥1`; its Y coordinate is `q'³s'` with `s'≥1`. If it preserves Y,
then `q'³ | q³s`. For each prime p, cube-freeness gives `vₚ(s)≤2`, so

```
3vₚ(q') ≤ 3vₚ(q)+vₚ(s)  implies  vₚ(q')≤vₚ(q).
```

Therefore `q'|q`. Write `q=q'd`. Both q and q' are congruent to 1 modulo
beta, so `d≡1 (mod beta)`. If `q'<q`, then `d>1`, whence
`q',d≥beta+1` and `q≥(beta+1)²`. But the source bound `J≤beta+1`
gives

```
q=beta*J+1 ≤ beta*(beta+1)+1 < (beta+1)².
```

Thus `q'=q`, contradicting the checked 76Y condition `3∤q'`.

The argument allows the target's F, alpha, w, z, first and auxiliary
witnesses, and other coordinates to change. It requires the **same beta and
ports**, the displayed source conditions, and preservation of Y. It does not
claim that changing Y is impossible, that a source zero exists, or that the
72-to-76 existence implication is false.

Cube-freeness is a substantive arithmetic hypothesis: with `J=2`,
`q=2beta+1`, `q'=beta+1`, `s=(beta+1)³`, and `s'=q³`, one has
`q³s=q'³s'` while `q'≠q`; for the actual beta, the two q values are in
different mod-3 classes. This is only a factorization control: it is not a
pair of graph zeros and imposes no transport or Pell norms.

[`check.py`](check.py) pins both graphs and relevant Lean sources, checks
555,940 finite cube-free rigidity candidates and 100 non-cube-free swap
controls, and checks the forward graph binding and old-carrier equation for
160 finite evaluations. These controls are not actual zeros or a Lean proof
of the preserving-Y statement. The valuation argument above and the separately
checked 76Y theorem provide the stated conditional deduction. Run
`python3 -I -S -B check.py`; retained output is [result.json](result.json).
