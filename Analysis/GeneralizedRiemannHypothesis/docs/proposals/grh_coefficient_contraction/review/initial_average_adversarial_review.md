# Independent review of initial-average normalization

Reviewed source commit: `1a59f50680e470fb5269bbe70c06f974c95ad930`.
The relevant AuxiliaryForms files are unchanged from the initial `d417d0b5b08edd4f5f67224fd310add7f1618ca0` snapshot.

## Verdict

The proposed normalization `firstPathDatum / C_D` is compatible with the downstream uniform period identity, p-adic integrality and archimedean estimates, provided the weighted-orbit theorem and the explicit twist-independent stabilizer cardinal are proved first. I found no hidden need for `C_D` to be a unit at the primes under consideration, and no need for an upper bound on its size.

The key point is to reprove integrality from the **normalized coefficients**, now roots of unity or zero. One must not infer integrality merely by dividing an old integral form by `C_D`.

## 1. Weighted-orbit/stabilizer check

The observed first point datum is a point indicator on the product of the false edge matrices modulo `I Q` and the true edge matrices modulo `I^b`; see `GridFirstColumns.lean:399–413` and `PathData.lean:63–125`.

The genuine finite acting group is the product of the false node groups over `R=O/(I^bQ)` and the true node groups over `B=O/I^b` at positions `1≤i<m`. The true position zero is replaced by the block embedding of the false position zero (`LevelCosets.family`, line 627), and the original redundant true-zero coset contributes its fixed cardinal `d=|GL_{b_0}(B)|`.

Although `LevelCosets.out` chooses representatives, the action on observed data and the character weight descend to this genuine quotient group. This uses normality of the true reduction kernels, surjectivity of reduction to `B`, and triviality of the relevant edge characters on those kernels (`GridFirstColumns.lean:564–583`; `PathData.lean:380–397`). One should not treat the chosen representatives themselves as a multiplicative section.

For the standard-inclusion tuple, descending from the anchored endpoints forces all false gauges to be identity modulo `IQ`, and all true gauges to be identity modulo `I^b`. The coupled initial node then forces the false-zero gauge to be identity modulo both ideals. The map

`O/(I^bQ) → O/(IQ) × O/I^b`

is injective because `(IQ)∩I^b=I^bQ`. This map is generally **not surjective**, and the proof does not need it to be. The remaining independent stabilizer factors are precisely the false interior congruence kernels.

Compatible CRT decompositions `R≅B×O/Q` and `R₀≅O/I×O/Q` identify each such kernel with `ker(GL_a(B)→GL_a(O/I))`. Thus its cardinal, and `C_D=d·∏|ker|`, are positive integers independent of the twist. The source's chosen/twist-place disjointness is essential here (`UpperBound/Objects/Rows.lean:74–105`), as is `b≥1`.

For a right action, a nonempty transporter is a coset `g₀H`. A finite character sum on `H` is either `|H|` or zero. Hence division by the fixed positive integer `C_D` yields a root of unity or zero at every edge assignment. No prior assertion that the stabilizer character is trivial is needed.

## 2. Uniform period scalar

`FirstPath.lean:422–436` gives the initial identity with a scalar `α` independent of the twist and initial forms. Periods are linear in the coefficient function. Replacing `Ψ₀` by `Ψ₀/C_D` changes that identity to one with scalar `C_D α`.

The local coefficient transformations are linear: Fourier is a finite linear sum; matching uses fixed representative evaluation and a character multiplier. Their choices can be held fixed while scaling the datum. The square constants, line-flip scalar, twist-dependent unit `c(ϑ)`, and its `HasAbsUpToNormPower` statement remain unchanged.

Consequently one may choose the new terminal coefficient family to be `Ψ/C_D`, and its terminal period to be `Ξ/C_D`. In `SpanningForms.lean:397–425`, the total period scalar is multiplied by `C_D`. The further factor converting the integral identity to a dual pairing at lines 635–656 is unchanged, so the final `β` may likewise be chosen as `C_D β`.

This is an existence comparison with coherent choices. It does not assert that Lean's arbitrary witnesses from two independently rerun existential proofs are definitionally related. For the migration, retain the chosen local transforms or use the explicit linearity identities.

## 3. The final normalization absorbs the scalar

At `SpanningForms.lean:686–697`, the proof chooses `s≠0` and `ε∈{0,1}` with

`s β = dualHook · (ε N)`.

There is no integrality, valuation-unit or absolute-value hypothesis on `s` itself. When `β≠0`, replacing `β` by `C_D β` allows the choice `s_new=s_old/C_D`. When `β=0`, the source's existing choice `s=1, ε=0` still works; the literal rescaling formula need not be imposed in that branch.

The subsequent proof uses the identity

`pair(normalized output) = dualHook · ε · (N Ξ_normalized)`.

It then proves arithmetic and size bounds for the right-hand side. The normalization scalar `β` no longer appears in those estimates.

## 4. Primes dividing the stabilizer cardinal

The denominator result `exists_mul_lastPathPeriod_mem_embValRing` (`SpanningForms.lean:223–271`) requires only the path-datum certificate, outer-level invariance, input gauges, and `p∤normQ(ϑ)`. The clearing factor is built from the unchanged kernel denominator and branching-pairing denominator:

`N = M_pair · liftDenominator^(2m)`.

Since the normalized initial values are roots of unity or zero, the existing local transformations preserve the original integral root-sum certificate. Therefore the same theorem applies to the normalized terminal data at every allowed prime, including primes dividing `C_D`. No factor `C_D` has to be added to `N`.

This argument does not cancel a nonunit in a valuation ring. It establishes that the divided coefficient function already lies in the integral coefficient ring before it is used in any lift or terminal pairing.

## 5. Complex automorphisms and size

The normalized initial values have absolute value at most one under every `σ:ℂ≃+*ℂ`, since automorphisms preserve finite order. The source's archimedean argument uses that coefficient budget and the same kernel/class-count estimates. Also `σ(C_D)=C_D` because `C_D` is a natural integer. No bound on `|σ(β)|`, `|σ(s)|`, or `C_D` is used: the exact equation `sβ=dualHook·εN` cancels the period scalar before the estimates at `SpanningForms.lean:720–740`.

Thus the claimed improvement in the **initial coefficient budget** is real. The final boundary-assignment count, class numbers, lift-denominator bound and branching-pairing estimates remain, so a corresponding reduction of a final global exponent is not automatic.

## 6. Required proof gates

* Descend both the observed action and the character weight from true representatives to the quotient groups.
* Prove the stabilizer equality, not just a bound, including the coupled zero node.
* Prove the compatible CRT kernel identification and twist independence of the cardinal.
* Prove root-or-zero values after division before invoking any p-adic result.
* Preserve uniformity of all period scalars and use coherent linear-transform choices when comparing normalizations.
* Keep the `β=0` case; never divide by an unproved nonzero period or proportionality scalar.

This review is a paper-level source check, not a Lean elaboration or kernel verification of the proposed replacement.
