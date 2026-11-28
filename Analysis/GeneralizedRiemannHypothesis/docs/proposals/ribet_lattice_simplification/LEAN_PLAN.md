# Lean integration specification (not compiled Lean)

Baseline: `835c3695d07c0f77060c5cc63f92eeb52a7d21c2` of ProveIt, project `Analysis/GeneralizedRiemannHypothesis/Lean/grh`. All paths below are relative to `src/` within that project. The first goal is unchanged theorem statements and constants, not a stronger GRH statement or an altered trust base.

## Stage 1 — direct constant-coefficient determinant (smallest independent change)

Target `New/Congruences/FirstOrder/FittingBlock.lean`, `exists_mem_fittingIdeal_addVal_constantCoeff_le` (line 65) and the last stage of `exists_mul_prod_X_mem_fittingIdeal` (137). Retain the original `formsMod`, `HasTriangleCost`, and the triangular step. This is independent of stages 2–3 and can be implemented with the existing lemma `Lib/General/Algebra/FittingIdealsAndLengths.lean:303`.

1. Define `ε` as `MvPolynomial.constantCoeff` applied coordinatewise. For the current relation module `T` (called `T` in the report), let `L` be its image over the coefficient ring O. It is an O-submodule. Use the hypotheses `Φ (p • v) ∈ T` and the basis relations to prove `p • ⊤ ≤ L`.
2. Apply `exists_matrix_addVal_det_le_length` to `L`, obtaining rows in L and a submodule S of vectors mod p having annihilator L. For each row choose a polynomial row in T mapping to it. Use determinant naturality under `constantCoeff` (existing `RingHom.map_det` API, check names against pinned Mathlib). This gives a polynomial determinant `d` in the old fitting ideal and a valuation at most `length O S`.
3. For each w ∈ S, construct the form `v ↦ dotProduct (ε (Φ v)) w` modulo p, followed by evaluation on z. These functions lie in `formsMod` for the module enlarged by zero-constant-term relations. They vanish on A₀, on all τ and τ′, and have equal values at φ_j and φ′_j for j ∈ I. The basis relation gives their values on the finite s as precisely the coordinates of w, so the map is injective. It commutes with scalar multiplication, and identifies the C-torsion of S with that of its image.
4. Bound `length O S` by its relative length modulo C-torsion plus `|s| * addVal O C`. The latter follows from inclusion into the C-torsion of `(O/p)^s` and the cyclic quotient length formula. For a sharper bound, establish equality with the torsion length of `O^s / L` using stage 2. Handle C=0 explicitly (F=0 when the old bound is infinite, and determinant of empty matrix otherwise).
5. Replace the old argument involving a second relative enlargement, `C • 1`, and descent by Fitting base change. Keep the scalar from the first enlargement and the entire polynomial product from `exists_ge_mul_prod_mem`. The final polynomial must be `c • C^|I| • d` (or the equivalent multiplication through scalar algebra maps), not its value at 0.

The conservative stage 1 only needs a determinant bound, not exact Smith invariants or an abstract theory of finite dual modules. The basis assumption is essential for injecting S into functions; it is present in the actual caller at `RibetMatrices.lean:769`.

## Stage 2 — finite dual cost, no Noetherian induction

Target `Lib/General/Algebra/FittingIdealsAndLengths.lean:680`, `fittingIdeal.exists_addVal_le_relLength`. Preserve the original statement as a compatibility wrapper; prove the stronger internal theorem without `[IsNoetherianRing R]`.

Suggested auxiliary interfaces (mathematical pseudocode, not asserted Lean syntax):

- `finiteDVRDual_extension`: for a submodule of a finite O-module killed by nonzero p, each O-linear map into O/(p) extends to the ambient module.
- `finiteDVRDual_length`: the dual into O/(p) has the same O-length as the module; double annihilator for submodules of the dual of O^n.
- `finiteDVRQuotient_generators`: for a finite module P killed by p, obtain finitely many generators with cyclic orders π^e_i and sum e_i = length(P). Can use Smith normal form of a full-rank sublattice of a finite free module, avoiding a general module structure theorem.

Use `DVR` and `QuotSpan p` from the source, not new incompatible classes. Suppress the source's `Unit`-indexed coordinate by a linear equivalence. Let L = preimage of N under Φ, A = annihilator(L) in the dual of O^n, E = evaluation on z, U = preimage of V under E, W = annihilator(U). W contains pO^n. Define P as the image of W in O^n/L. By extension and double annihilator, the restriction map A → P* is onto with kernel A∩U; the map A → formsMod/V∩formsMod has exactly the same kernel. Their lengths agree even if E is not injective. No assumption that z spans the source is permitted.

Take generators of P, lift them to W, and let K be N plus their R-spans after applying Φ. The one-row Fitting transfer lemma at line 516 already handles each generator, since π^e_i Φ(w_i) belongs to N. Iterate over this finite list, tracking the product of π^e_i; the multiplier has valuation exactly the relative length. Prove K contains every Φ(w) annihilated by all Ψ with Ψ∘z in V. No Noetherian induction on K is needed.

The finite duality facts can be developed using free lattices and Smith diagonalization. Extension is explicit in diagonal coordinates: if a_i≤h and a map on π^a_i O sends its generator to u_i, then π^(h-a_i) u_i=0, so choose v_i with π^a_i v_i=u_i. The finite length theorem follows by summing cyclic lengths. This needs no injective envelope theory. Keep `mem_of_forall_form_eq_zero` until all other callers are audited. Delete `exists_pow_smul_notMem_and_succ_mem` and `map_mkQ_formsMod_lt` only if no reverse references remain and the full project rebuilds.

## Stage 3 — direct row-lattice determinant

Target `Lib/General/Algebra/BlockFittingBound.lean:36,157`, the two `exists_rows_addVal_det_le` variants. Preserve their original hypotheses and row outputs. Keep `DivisibleQuot`, `divQuot`, and related public lemmas until a full reference audit.

1. Let L be the O-span of rows of all horizontally concatenated ψ(t), t∈N. Prove equality of its annihilator and the submodule of simultaneous solutions of ψ(t)w=0. This holds over both O/(p) and K/O, and does not use surjectivity.
2. Use freeness and finite generation of submodules of finite free modules over a DVR. A basis row matrix with possibly fewer rows than columns may be padded with zero rows *for Smith diagonalization only*. This is not the old enlargement by pO^n. For finite precision, the Smith-coordinate length is the sum of truncated valuations. If it is less than addVal(p), the rank is full and each exponent is strictly less than addVal(p). For divisible coefficients, a missing direction gives arbitrarily long cyclic submodules, contradicting the finite length bound. On finite cyclic factors use `divQuot` or the explicit quotient K/O to get the length equality.
3. For each chosen basis row, express it as a finite O-linear combination of rows of ψ(t). Use surjectivity to lift elementary matrix units with scalar coefficients. Left multiplication by such a lift and addition in the left submodule N allows any d chosen rows to be assembled in a single t∈N. Group the basis rows into q blocks, with `Matrix.comp` (or its pinned equivalent) arranging them in the exact original order. The flattened determinant is the actual basis determinant, not a congruent approximation.
4. Handle empty block dimensions by the empty matrix and rank zero. Keep the strict inequality on the finite precision length: `L=π^(h+1)O` is a counterexample when the threshold is weakened to h.

Unchanged downstream callers include `FittingBlock.lean:645` and `RibetMatrices.lean:539,769`. Do not alter the fixed polynomial coefficient extraction, the Hecke algebra, or the Selmer hypotheses.

## Acceptance and measurement

At the pinned revision, build a separate experimental branch; do not overwrite the original proof. Locate dependencies with `rg` for all affected declaration names and the private helper names. Preserve original theorem types; temporarily give alternatives fresh names and use `#check` and small adapters to test compatibility. Run after each stage:

```sh
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
```

The source README provides its additional independent-checker procedure. Confirm the five public statements have the original types and no `sorry`, `admit`, or new axioms in their transitive closure, not merely a successful build of one module. For fair measurement compare both clean and incremental build time at the same revision/toolchain and count total noncomment Lean lines in the changed files plus any added helper modules. Report dependency-closure changes as well. The roughly 330 lines of touched regions in the paper are not net deletions. If the shared duality library costs more code than it saves, stage 1 is still a separately usable local simplification. There is no compiled Lean patch or measured performance claim in this archive.
