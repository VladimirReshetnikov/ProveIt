# Independent Lean Carrier65 front review

Result: PASS for the literal arithmetic front and positive-zero factor
decomposition. This review does not establish fixed-port native calibration,
an end-to-end consistency equivalence, the operation count, or the degree in
Lean.

Reviewed complete sources:

| Source | SHA-256 |
|---|---|
| `Lean/DiophantineConsistency/Carrier65.lean` | `be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154` |
| `Lean/DiophantineConsistency/Carrier65Checks.lean` | `a9043cc8a1b199f4d8161403717293b5b8c942ba2b0a4782cc25c4ff35953c4a` |
| `candidates/one-page-padding-staircase-carrier65-2011/equation.tex` | `a48ac1f5bc498bfdbf300c7050332ecaa28af1fc43f27d86b0879a79bd38714e` |

Every coordinate agrees with the printed order
`J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma`. The ports are
`beta,K,MC,MF_source`; the last port already includes its beta shift and is
used exactly once in the rank. All displayed blocks, including the quotient
carrier `tau`, auxiliary norm, transport factor, and scaled strong factor,
agree with the actual TeX. The polynomial evaluation theorem binds the
multivariate polynomial to this literal expression.

The proof cancels the positive discriminant before applying the integer-unit
argument. I also read the invoked consecutive-Pell negative-unit theorem,
the modulo-four strong and auxiliary obstructions, and the product-unit
lemma. Their substitutions are correct: the first parameter is at least two,
the main and strong discriminants are one below a square, and the auxiliary
coefficient is a square. The four excluded negative signs leave the transport
factor equal to one. Neither a sign of `tau` nor positivity of `C` or the rank
is assumed. The theorem requires positive beta and all fourteen coordinates
positive; the other three ports may be arbitrary integers.

The focused checks bind the slots symbolically and exercise the source-mask
shift numerically, including a negative-tau case. Independent command:

```text
lake build DiophantineConsistency.Carrier65 DiophantineConsistency.Carrier65Checks
```

This passed (the already-built modules were replayed). Printed theorem
dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`. No source edits were requested. This receipt is an
independent source and theorem-scope review, not a new rendering review of
the unchanged 2011 page.
