# Two conditional boundary constructions for the 76 transport candidate

The 76 candidate replaces the 77 graph's positive `alpha` by a positive input
`C`, removes `C=q−F−alpha`, and writes the rank gap as
`q*(q−F)−C`. Recovering the *same tuple* in the 77 graph requires
`q−F−C>0`. The constructions below show why deriving that inequality for
every 76 zero is a substantial additional claim. They are exact algebraic
transformations of the displayed graph relations; they are not Lean proofs.

Write

```
q = beta*J + 1
C = q - F - alpha
G = (q-1)*(q-F) + alpha
R = G*(q^2-1) + J*(MC+q*MF)
Lt = (K0+w)*C - F - z*(q-1).
```

For a positive 77 tuple with `Lt=0` and natural ports, `C>0`: the transport
equation says `(K0+w)*C=F+z*(q−1)>0`. Therefore `q≥3`, `beta>0`, and
`q²−1 = beta*J*(q+1)`. The graph uses `F`, `alpha`, `z`, `K0`, and `MC`
only through `q`, `R`, and `Lt` in the five residuals. The transformations
below preserve `q` and `R` and preserve zero transport. They therefore
preserve all five residual values and the output, even when that output is
not zero.

## Changed ports: boundary `q−F'−C'=0`

Starting with any positive 77 tuple with `Lt=0`, put

```
delta = G - (q-1)
F' = q-1             C' = 1              z' = w
K0' = (w+1)*(q-1)-w  MC' = MC + delta*beta*(q+1).
```

Keep `beta`, `MF`, `J`, and all other witness coordinates. All new witness
coordinates are positive and both new ports are natural. Indeed `q−F≥2`, so
`delta=(q−1)*(q−F−1)+alpha>0`; also `q−1≥2` gives `K0'≥0`. The new
rank gap is `q*(q−F')−C'=q−1`, and the added `MC` contribution is exactly
`delta*(q²−1)`, so `R'=R`. Moreover

```
(K0'+w)*C' - F' - z'*(q-1)
= (w+1)*(q-1) - (q-1) - w*(q-1) = 0.
```

Thus a seed 77 zero would give a full 76 zero on the boundary
`q−F'−C'=0`. Both `K0` and `MC` may change, so this does **not** give a
fixed-port counterexample.

## Fixed ports: strict violation under extra seed hypotheses

Assume additionally that the seed has `F≥2` and
`(q−1) ∣ (K0+w+1)`. Set `L=K0+w` and keep **all four ports** and all
witnesses other than these three:

```
F' = F-1
C' = C+q
z' = z + (L*q+1)/(q-1).
```

The quotient is a natural integer because `q≡1 mod (q−1)` and
`L+1≡0 mod (q−1)`. The new inputs are positive. The rank gap is unchanged:

```
q*(q-F')-C' = q*(q-F+1)-(C+q) = q*(q-F)-C = G.
```

Writing `d=(L*q+1)/(q−1)`, the new transport residual equals
`Lt + L*q + 1 - d*(q−1) = 0`. Hence `R` and all five residuals again match
the seed, but

```
q-F'-C' = 1-F-C < 0.
```

Consequently, if a 77 zero satisfying the two extra seed conditions exists,
there is a 76 zero at those **same** ports that does not map back by the
strict coordinate substitution. This does not show that there is no other
77 witness at those ports; the seed itself is one. It therefore does not
refute the fixed-port *existence* equivalence.

## Scope and finite checks

No actual 77 seed zero is constructed here, and no existence of a seed with
the fixed-port hypotheses is claimed. These are conditional obstructions to
the proposed same-tuple inequality, not a counterexample to the existential
equivalence or to the fixed current coefficients. An alternative witness
normalization could still prove that equivalence.

[`check.py`](check.py) externally evaluates both pinned graph JSON files on
randomly generated positive tuples with zero old transport. The changed-port
construction passed 482 cases, and the fixed-port construction passed 460;
all five residuals and outputs matched. None of those seed outputs was zero.
The finite check uses exact integer arithmetic and tests graph transcription
and these examples only; it does not establish the quantified algebra or any
Lean theorem. Reproduce it from the repository root with:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube76-boundary-obstruction/check.py
```

`check.py` SHA-256:
`5a5eb2e8c4197df9faad8926be9842c1cf5e99c74654b6cec3ee7f8b06eaf8cf`.
