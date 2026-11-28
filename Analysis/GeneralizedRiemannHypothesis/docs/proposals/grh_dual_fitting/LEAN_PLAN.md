# Interface-preserving Lean migration

Baseline: `9050b04000647d588d0c78d945180abcd3b0bcf7`, under `Analysis/GeneralizedRiemannHypothesis/Lean/grh`. Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` are reported in the project. This is a specification, not elaborated Lean syntax. No new axiom, `sorry`, or change to the final theorem statements is acceptable.

## Stage 1 — specialization at zero (lowest risk)

Replace only the body of `New.Selmer.exists_mem_fittingIdeal_addVal_constantCoeff_le` in `New/Congruences/FirstOrder/FittingBlock.lean` (65–102).

1. Define the coordinatewise `constantCoeff` map `εs : (s → MvPolynomial J O) →ₗ[O] (s → O)` and `L := T.map εs` (restrict scalars as needed). Prove its inverse image is `T ⊔ ker constantCoeff • ⊤`. Forward direction: every polynomial row minus its constant row is in `ker constantCoeff • ⊤`, since the index type is finite. Backward direction: map the decomposition.
2. Show `p • ⊤ ≤ L`. For a standard basis row use `h_basis g` and `hT_smul_p (z g)`; after specializing, `p • e_g` is in `L`. Sum over the basis.
3. Invoke `New.exists_matrix_addVal_det_le_length L hp …` from `FittingIdealsAndLengths.lean:303` to obtain actual rows `Bbar` of `L`, with determinant bounded by the length of its annihilator in `s → QuotSpan p`.
4. Embed that annihilator into `formsMod Φ z T₀ p` using the map `Ψ(w) = εs(Φ w) · u`. It kills `Φ⁻¹ T₀`; its evaluation at `z(g)` for `g : s` equals `u(g)` because `εs (Φ (z g)) - e_g ∈ L`. Thus the embedding is injective and evaluation on `s` also detects all functions in `formsMod Φ z T₀ p`: `Φ` surjects onto the specialized quotient by `L` using `h_basis`.
5. In the target solution module, its `C`-torsion embeds into `(QuotSpan p)[C]^s`. Use the length formula and `length_quot_span_eq_addVal` to obtain `length Z₀[C] ≤ #s * addVal O C`. For `C = 0` the original upper bound is infinite (unless `s` is empty, handled separately). The sharper `min` is optional; avoid new downstream arithmetic.
6. Lift each row `Bbar g` to `B g ∈ T`. Set `d := Matrix.det B`; membership in `fittingIdeal T` follows directly from its generating set. `RingHom.map_det` identifies its constant coefficient with `Bbar.det`. Combine relative length + length of intersection.

This stage can use existing source lattice duality without implementing Smith normal form anew. The paper's exact equality for a chosen basis is stronger than the contract and optional for this stage. Retain the declaration's precise signature and all callers.

## Stage 2 — direct relative Fitting cost

Target: `Lib/General/Algebra/FittingIdealsAndLengths.lean:680`. Current proof uses Noetherian induction. Preserve the public lemma and, if useful, add a stronger lemma without `[IsNoetherianRing R]` and with canonical `K`.

Definitions in mathematical notation:

- `L = Φ⁻¹ N`, `M = O^n / L`, `pM = 0`.
- `D = Hom_O(M, QuotSpan p)`; identify with the compatible linear maps in `formsMod`.
- `ev : D →ₗ[O] (G → Unit → QuotSpan p)` by composition with `z`; `Z = range ev`.
- `U = ev⁻¹ V`; `M' = {m | ∀ λ ∈ U, λ m = 0}`.
- `L'` preimage of `M'` in `O^n`; `K = N ⊔ R-span(Φ(L'))`.

Prove `length M' = relLength Z V` by finite duality. An implementation may avoid a complete bidual API: show restriction of homomorphisms into `K/O` is onto by divisibility over a DVR, then use the natural isomorphism of `p`-torsion with `QuotSpan p` (`BlockFittingBound.divQuot` infrastructure may need moving to a lower import layer). Alternatively prove finite pairing exactness via existing elementary divisors or the annihilator lemma at line 303. Beware of creating an import cycle. The function index `G` need not be finite; only `O^n/L` is finite length. Do not assume evaluation is injective or `V ≤ Z`.

Use a cyclic decomposition of `M'` over the DVR to choose lifts `w_i ∈ L'` with `π^(a_i) • Φ(w_i) ∈ N`, sum `a_i = length M'`. A composition series of the *fixed finite module* `M'` is also enough: add its cyclic simple layers in order and charge a uniformizer per layer. This retains the conceptual reduction to one finite module and avoids induction on arbitrary polynomial submodules. A cyclic decomposition gives the cleaner determinant certificate.

The existing lemma `fittingIdeal.mul_mem_of_smul_mem` (516) or its finite-product form (547) yields the inclusion by induction on the finitely many generators. Use the finite module's quotient-length identity, not the old strict-drop lemma. Keep the old API as a wrapper. Only delete `exists_pow_smul_notMem_and_succ_mem` and `map_mkQ_formsMod_lt` if repository-wide reference checks show no other uses.

## Stage 3 — main-block relation rows

Targets: `Lib/General/Algebra/BlockFittingBound.lean:36,157`. Define a row lattice `W` as the span of all rows of the flattened `ψ(t)`, `t ∈ N`. Prove row packing by left multiplication by preimages of matrix units (the surjectivity hypothesis). This is the same matrix-unit mechanism already used by the source; the change is to apply it to *actual* row-lattice generators/basis, rather than to a matrix constructed modulo a large power.

For the divisible variant, the solution module is `Hom_O(O^(ι×d)/W, Frac(O)/O)`. Show full rank: a proper fraction-field row span gives a nonzero orthogonal vector; clearing denominators and scaling by a uniformizer yields an integral primitive orthogonal vector. Its multiples with coefficients in `Frac(O)/O` give a copy of the divisible quotient inside the solution space, contradicting finite length. Show infinite length via the embeddings `divQuot (π^m)` with arbitrary `m`.

Choose a nonzero annihilator `p` of the full-rank quotient. Apply the existing finite annihilator lemma directly to `W` (not `W + p O^(ι×d)`, which now equals `W`) and use `divQuot` to bound its finite solution length by the divisible solution bound. Pack its actual rows into `N` and flatten. This route avoids new Smith normal form infrastructure and any determinant congruence lifting. Handle empty dimensions explicitly.

For the finite variant: either use elementary divisors, or observe that the finite annihilator of `W + p O^(ι×d)` has length strictly below `v(p)`. The quotient by that enlarged lattice is killed by some smaller power of a uniformizer; a standard finite-generator Nakayama argument then implies `p O^(ι×d) ⊆ W` (see report for elementary divisor version). If the direct proof takes more code, keep the old finite lemma as a compatibility result and replace only the divisible path.

## Stage 4 — downstream invariants

Run the unchanged `exists_mul_prod_X_mem_fittingIdeal` (FittingBlock:137). Its triangle uses both paired relations and `HasTriangleCost`, neither of which changes. Run `exists_block_rows` (FittingBlock:619), then `exists_tiedRows_addVal_det_le`, `exists_mem_fittingIdeal_character`, and `nonempty_characterRows` (RibetMatrices:539,724,933). Run the original gluing and `exists_isCommonRibetElement_addVal_le` (RibetLemma:218,551), followed by `ribet_columns` and `denominatorLe_clearingBound`.

Do not infer that a general member of a Fitting ideal is a single determinant. The specialization result gives a single determinant at one stage; the character gluing still uses finite sums. Do not modify the analytic endpoint, Hecke constants, Selmer conditions, good labels, level choices or twist selection. Keep original inequality with `#s * v(C)` rather than optimizing the bound in a first merge.

## Acceptance and measurements

1. Create a branch from the pinned baseline and reproduce its checks before changing anything. Use the existing project toolchain; do not substitute a different Mathlib. `lake exe cache get` and `lake build` (the baseline README documents the build requirements).
2. Implement each stage as its own commit. Build the affected modules and all dependents, then `lake build`. Compare theorem statements using the baseline declarations. `lake env lean scripts/PrintAxioms.lean` and the project's comparator should report the same allowed axioms and unchanged five public statements.
3. Perform independent kernel replay using the baseline's documented process. No result of that replay is claimed here.
4. Audit removal candidates with `rg 'exists_pow_smul_notMem_and_succ_mem|map_mkQ_formsMod_lt|exists_mem_fittingIdeal_addVal_constantCoeff_le|exists_rows_addVal_det_le' src`. Inspect actual imports and references, not just text occurrences. Never remove reusable `divQuot` or generic Fitting lemmas without checking callers.
5. Compare total nonblank noncomment Lean lines across the modified dependency closure, including helper modules; also compare declaration count, cold build time and memory under identical settings. A smaller theorem body that adds a larger helper dependency is not a net simplification. No quantitative savings are asserted until such comparison is run.
