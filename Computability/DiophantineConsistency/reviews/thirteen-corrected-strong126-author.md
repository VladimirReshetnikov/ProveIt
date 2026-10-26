# Corrected thirteen-variable strong factor: author receipt

Author: `/root/controller_certificate`. Date: 26 October 2026. This is author
validation, not an independent review. The author also wrote the retained
Carrier65 arithmetic dependency and several current native word/carry modules;
the new current consistency endpoint composes the root-authored
`CurrentPositiveZero2011`. No dependency freshness beyond the two newly compiled
modules is claimed here.

## Frozen files and fresh direct builds

| File | Lines | SHA256 |
|---|---:|---|
| ThirteenCorrectedStrong.lean | 155 | 57729066535acf1909d30ea5de0b4b78e1ac6f1ae11a126e1c2c4526cc546efe |
| ThirteenCorrectedStrongChecks.lean | 50 | 481f520df1e3ff05efc7869e9c118596e3b9967cac097527c1a7de77ddfe109f |

I read the whole new sources before execution, including each subsequent small
change. Final commands, serially from the repository root, were:

```bash
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/ThirteenCorrectedStrong.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenCorrectedStrong.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/ThirteenCorrectedStrongChecks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenCorrectedStrongChecks.lean
```

Both exited0. The final main log is empty. The checks emit eleven intended axiom
reports, all subsets of `propext`, `Classical.choice`, `Quot.sound`; no sorry,
unsafe oracle, new axiom, native_decide, cap raise, or duplicate Lake build was
used. Final object hashes are respectively
`9c0b942bfcb02ecbdfde0e0e691862d9935bae98617bb874ac8ea5b8334f7142` and
`5de1ec7f248a31159208086683b1832e12ed65ee30159db1186c778ccef821c7`.
Logs are `/tmp/thirteen-corrected-strong-main.log` and
`/tmp/thirteen-corrected-strong-checks.log`.

The first map-proof drafts left reduced Fin-index match expressions, and then
mapped numerals, unsimplified. Replacing `simp only` with ordinary simplification
plus explicit `map_ofNat` discharged the same statement. One no-op tactic was
removed. The original equivalence/sign proofs passed; no mathematical premise
was weakened. The final exact coefficient-cancellation ring lemma was added and
both final files were freshly replayed afterward.

## Mathematical boundary

The new strong factor is `Z-(b*i*c)^2*(P-1)`. The complete ring identity relates
the two unit-product polynomials. `first_ne_neg_one` uses the actual
`Carrier65.first_shape` and `firstParameter_ge_two` on the positive parent
assignment; it assumes no zero or first-norm equality. `first_eq_one_of_zero`
and `first_eq_one_of_old_zero` then independently derive P=1 from their own
integer unit products. This proves equality of the entire positive zero sets
at the same thirteen coordinates, without assuming signs for tau, C, rank or y.

`value_map`, `polynomial` and `eval_polynomial` give the actual commutative-ring
expression and thirteen-variable MvPolynomial. The endpoint
`no_current_positive_zero_iff_conZFC` uses the complete current2011 port tuple
`CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)`, with source MF shifted once.
It composes the accepted external Lean consistency theorem. It is not an
internal object-language ZFC derivation and does not decide consistency.

## Literal graph and exact degree

The new isolated research namespace is `research/thirteen-corrected-strong126`.
Its script was newly authored and completely read before execution; it executes
no incoming or project modules. It reads inert pinned JSON/port inputs only.

| Artifact | SHA256 |
|---|---|
| audit.py | d185e03bff041eb2d581c9f0f49d8d157b0ea275be3d4d45c9c0cb9498892f6d |
| polynomial.json | e6deeec7f6a298f47e4247c5868e39d7d9caa6431b738ef6b99e822e7183a358 |
| CERTIFICATE.json | 7d7b6230409776e0fc79a627cc86665f8fd45aca8d94974a6eb4204172e585a5 |

Write, normal and `-O` runs passed, with deterministic byte equality. The checked
graph has73 live integer-leaf operations:40 products,17 additions,16
subtractions. All13 independent positive variables and four ports remain live.
The whole cut-polynomial identity is checked from the actual old/new DAGs.
Full expansion resolves the323-term main norm and353-term corrected strong
coefficient; all gate leaders are computed, including both cancellation sites.
The final degree126 leader has72 terms and contains the nonzero coefficient
`-256*beta^70` at witness monomial
`J^70*gamma*i^2*eta^11*w^9*s^19*f^10*T^4`.

This exact-degree claim is checked ordinary finite polynomial arithmetic, not
a new Lean totalDegree theorem. The Lean cancellation lemma and complete
positive-zero-set theorem are separate kernel-checked statements.

All3297 frozen2011 coefficients are read, every whole port rebuilt, and all four
current materialized port files byte-compared. The complete raw cost remains
47313 bytes. The old normalized graph's stored2471 constants are not conflated
with this2011 specialization. The audit rejects six actual graph corruptions,
and separately checks the wrong-sign correction changes the whole polynomial.

This checkpoint is a two-operation/two-degree tradeoff from13/71/128, not a
minimum or a dominating replacement. It adapts the earlier fifteen-variable
`ShortReducedStrong` correction; no novelty claim is made. No maintained page,
accepted source, fixed port, shared document or Git state was changed.
