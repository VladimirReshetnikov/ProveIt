# Independent review of fresh proof-simplification candidates

Source pin: `efa64ca941cdae37bb6f7fc5093ae8bb69296ca3`.
Reviewer scope: mathematical arguments, novelty against the 22 a–v packets and current incoming README, exact changed statements/data, and the meaning of the supplied validation receipts. This is independent source review, not a second clean build of every dependency or client.

## Final disposition

- PASS: Jones semantic-lemma reuse; positive auxiliary-norm gap; shared affine carrier-step bound; monomial-list interpretation bridge; helical diagonal periodicity; deterministic function-witness elimination.
- EXCLUDE AS REPEATED: ratio coprime-divisibility witness cleanup.
- Eight candidate source files remove 94 physical lines on the pinned baseline. Three complete modified modules account for 19 lines; exact theorem/extracted-source kernels plus static integration patches support the other 75. No full-project replay or speedup is claimed.
- Exact final patches and recorded file hashes were checked independently. The temporary helical patch/hash mismatch was resolved. The baseline Syntax receipt explicitly discloses its reconstruction from observed output after a storage write failure.

## 1. RatioReparameterization: conservative novelty rejection

**Disposition: omit from the new-idea set.** The suggested `combined_dvd_iff` proof is mathematically sound and targets a declaration not explicitly changed by the previous packets. However, its main simplification—retaining divisibility evidence and composing closure lemmas rather than unpacking and rebuilding quotient witnesses—is already advertised by packet l.

Exact primary comparison: `research/lean-proof-simplification/2026-10-26l/report/report.tex`, section "Idea 3: keep divisibility witnesses abstract", lines 315–367. The old report explicitly recommends `dvd_sub`, `dvd_add`, and `dvd_neg`; it says that opening an existential is inappropriate when the quotient is immediately repackaged, and explains the argument as additive closure of a principal ideal. Its concrete client is signed Pell residue transport, but the proposed technique is intentionally general.

The new ratio candidate's reverse direction is precisely closure under products and addition (`mul_dvd_mul_right`, `mul_dvd_mul_left`, `dvd_add`) in place of explicit witnesses. Its forward direction makes the already-existing coprime cancellation proof more compact. The mathematical two-channel equivalence itself is already the maintained theorem's statement, so it is not a new algebraic result. Calling it a new "coprime fusion" would further confuse it with prior Diophantine construction work summarized in the incoming README.

A non-novel application to another target can be useful maintenance work. Under this user's strict request to avoid repeating ideas, it should not be a fresh proposal or contribute to the claimed incremental saving. This is a **novelty rejection, not a correctness failure**.

## 2. Deterministic function witnesses in representation composition

**Mathematics: PASS.** The exact logical equivalence is

`(∃ a, P a ∧ ∀ i, a i = f i) ↔ P f`.

Function extensionality rewrites the final conjunct to `a = f`. Equality substitution then removes the existential. No finite cardinality, nonempty-domain hypothesis, choice of fresh witnesses, or computational extensionality assumption is needed. In particular, the zero-arity `Fin 0` case is retained.

**Data and statements: PASS by direct diff review.** The changes in `ComposeRepresentation.Rep.compose` and `DirectComposition.GraphRep.composeDirect` affect only the final `ofIff` proof. All binders, predicate types, `index` and `slot` maps, `rows`, reindex/conjunction/existsBlock constructors, witness counts, and stored expressions are unchanged. The supplied `Compatibility.lean` reconstructs the actual original definitions and closes both complete-record equalities with `rfl`; this is stronger evidence than merely comparing counts.

**Novelty: PASS, narrowly stated.** Earlier a–h naturality/Fin-block interfaces remove assignment and witness-layout bookkeeping. Packet m consumes a Boolean/slack certificate in `QuadraticBoolean`. Neither advertises removing the function-valued deterministic intermediate remaining in these two composition proofs. Do not describe generic existential simplification as new; the additional target and residual extensional equation are the substantive difference.

**Evidence scope.** `modules-validation.log` reports zero exits for `Representation`, `ArithmeticRepresentation`, `ComposeRepresentation`, and `DirectComposition`. `final-validation.log` reports acceptance of both `rfl` record checks. Those logs do not establish that all downstream representation clients were rebuilt, nor do they establish unchanged old/new axiom sets unless the separate paired reports are supplied.

## 3. Helical row-zero by ordinary periodicity

**Mathematics: PASS.** Define `f(s) = T(x+w*s,t-s)`. The existing hypothesis `T(x+w,t-1)=T(x,t)` gives `f(s+1)=f(s)` after two ring identities. Applying integer-periodicity invariance with period 1 at `s=t` gives `f(0)=f(t)`, hence `T(x,t)=T(x+w*t,0)`.

Every signed integer time and weight is covered. Zero or negative `w`, and zero or negative `t`, require no extra case. No spatial or vertical period, positive dimension, allowed tile, Start uniqueness, nonempty finite modulus, or machine computation assumption is introduced. The transformation uses the existing universal helical identity, not an assumed quotient-factorization theorem.

The additional demonstration `helix_iff_unique_factorization` is also sound. The forward factor is explicitly `F(z)=T(z,0)`; any other factor agrees with it at time zero. Conversely, factoring through `x+w*t` makes the helical shift preserve the factor's argument. This is an explanatory strengthening of the same idea, not another independent simplification or an integration claim about the finite quotient.

**Data and statements: PASS by direct diff review.** Only `row_zero_of_helix`'s proof body changes. `periodic_emod`, period transfer, `quotientWord`, address orientation, the exact marked-word binding, all assumptions, and the finite word data remain untouched. The old proof already uses a two-sided integer induction; the new proof delegates that standard argument to the periodicity library.

**Novelty: PASS.** No previous proposal targets `HelicalQuotient`/`row_zero_of_helix` or the diagonal pullback. The nearest u/v centered integer-induction proposals concern *guarded interval propagation*; i/l predecessor reflection concerns *finite invariant subsets*. Neither removes this helical coordinate proof. Packet o's advice against a generic additive quotient framework is compatible with this local library application.

**Evidence scope.** The exact theorem is compiled in `StructuralKernels.lean` under `Mathlib.Algebra.Ring.Periodic` and `Mathlib.Tactic.Ring`; its reported axioms are `[propext, Quot.sound]`. The supplied initial module log does not compile the complete changed `WangTiles942HelicalQuotient` module. Generic theorem compilation is not complete module/downstream validation, even when its mathematical statement is identical.

## 4. Artifact consistency finding

During review, the helical candidate had a linter-only edit from `using 1 <;> congr 1 <;> ring` to `using 1; congr 1 <;> ring`, while the patch, kernel and metrics still described the earlier bytes. The structural author acknowledged this as an in-progress edit and is synchronizing the final files. This is not a mathematical defect, but exact final source, patch, hashes, and compiler receipts must be brought into agreement before release.

At the initial review point, both representation candidate hashes already matched their metrics. The helical candidate hash was `4b92c40aa3d4cbdd342176787322921289406807686724b1e7fd25b292701a90`, while the metrics recorded `8672a34e48b64fbc74aaa8b700a2d636d70445fa54270052e97a3e78d463c67c`. Treat this paragraph as a finding awaiting the final reconciliation below.

## 5. Remaining review boundary

The subsequent sections record the later SyntaxCoefficients and Jones reviews. The carrier affine-step candidates are reviewed when their final patches and validation outputs are supplied. Neither the earlier compilation receipts embedded in prior packets nor compilation by a generic demonstration establishes current complete-client replay. No full endpoint replay or speed improvement is inferred by this review.

## 6. Final structural reconciliation

**Artifact finding resolved.** Recomputed SHA-256 values now agree with all three rows of `structural/metrics.json` for both original and candidate sources. Independently regenerating the entire unified diff from those source pairs yields a byte-for-byte match to `structural/structural.patch`. The candidate and exact compiled kernel now use the same final `using 1; congr 1 <;> ring` tactic sequence.

The final `structural/final-validation.log` reports zero exits and no warnings for the exact kernel and compatibility files. It prints paired old/new axiom sets for both constructors; each pair agrees on `[propext, Classical.choice, Quot.sound]`. Whole-record `rfl` checks also pass. This resolves the artifact-consistency finding without changing the evidence boundary: the complete helical tile module and all downstream clients are still not rebuilt in this scope.

Verified physical-source accounting is 71→66 lines for ComposeRepresentation, 77→72 for DirectComposition, and 147→137 for WangTiles942HelicalQuotient, totaling 20 removed lines. There is no new production helper; the demonstration kernels are separately supplied evidence. Only the first ten lines belong to complete-module-compiled edits; the other ten belong to the exact-theorem-compiled proposed integration patch.

## 7. SyntaxCoefficients list-semantics bridge

**Mathematics and maintained data: PASS.** The private `interpret_eq_sum` theorem identifies the exact recursive interpretation of a list of monomial pairs with the corresponding `List.map` followed by `List.sum`. It does not replace or normalize the list itself. The subsequent proofs use append distribution, negation of a sum, the ordered flatMap product and its two distributive sum laws, and `map_list_sum` for `MvPolynomial.coeffAddMonoidHom`.

The monomial multiplication proof correctly uses `exponent_add`; coefficient extraction correctly uses `exponent_inj`. These are the necessary bridges between the executable exponent functions and Mathlib finitely supported exponents. Duplicate monomials remain duplicate terms in executable data and contribute with their original multiplicity to the sum. Empty lists, negative coefficients and cancellation are covered. No injectivity/distinctness/nonzero-length premise is added, so `Fin 0` remains valid.

The direct diff changes four existing public proof bodies, removes the now-unused private `interpret_leftMul`, adds the private bridge, and adds `Mathlib.Algebra.BigOperators.Ring.List`. The definitions `negate`, `multiply`, `expand`, `coefficient`, `exponent`, and `interpret`, and all original public theorem statements and simp attributes, are unchanged. The bridge is deliberately not a global simp theorem. Five separate list inductions become one bridge induction; the structural induction on expressions in `interpret_expand` is retained. Source size is 120→111 lines, counting the helper and import.

**Novelty: PASS in this exact scope.** Earlier coefficient-homomorphism work concerns row catalogs, arithmetic coefficient formulas, and sparse-row certificate verification. No earlier report or patch targets `SyntaxCoefficients` or these monomial-list interpretation inductions; its only corpus occurrences are source-tree inventories. The new step is identifying an existing custom list fold with library summation, not inventing a new generic coefficient normalization framework.

**Observed validation.** The exact full candidate module compiles with exit 0 in `audit/syntax/validation.log`, including its endpoint `coefficient_expand` axiom print `[propext, Classical.choice, Quot.sound]`. The parent separately observed a successful baseline compilation with the same three endpoint axioms, but initial transcript persistence failed because the workspace filled; the final report should retain that fact about the reconstructed receipt if it relies on it. No all-client rebuild or performance comparison is inferred. Final patch/metrics reconciliation remains to be recorded when available.

## 8. Jones expression-evaluation reuse

**Mathematics, statements and stored syntax: PASS.** The five evaluation bridges `eval_rad`, `eval_wt`, `eval_dvsr`, `eval_dvnd`, and `eval_marg` already prove the required formulas in `JonesSyntax`. The downstream `ExecutableJones` versions have the same statements, with only namespace qualification and beta-reduced notation for `Expr.eval`. They perform the same simplifications over the same `RingVars` definitions. The downstream file already imports `JonesSyntax`.

The reviewed `JonesSyntax` candidate differs from baseline *only* by removing `private` on those five theorem declarations. Thus their statements and proof bodies are otherwise byte-identical, and no new simp attributes or executable definitions are added. `ExecutableJones` deletes the five private duplicates and qualifies the five lemma names used in `eval_withInput`. All existing public declaration types, variable ordering, `rankCode`, `syntaxVars`, `withInput`, expression construction, witness data and other executable definitions are unchanged. There are five newly public theorem names; this should be reported as an API extension rather than saying the entire public name set is unchanged.

**Novelty: PASS at this concrete semantic interface.** No earlier report or patch promises exposing these five Jones bridges; the module names occur only in source-tree inventories. The earlier shared `ratioValue`/99-node tails and earlier relocation of degree/rename facts concern different operations and consumers. This proposal does not re-propose a generic homomorphism framework or coefficient-table compression. It deletes actual duplicate mathematical proofs by making their existing provider usable.

**Evidence boundary.** `JonesBridgeHarness.lean` imports the actual `Representation` layer and contains literal extracted definitions of `Jones1982.Nine.Vars`, its operations, `NinePolynomial.RingVars`, its operations, and the original five provider proofs. It then checks each old downstream theorem statement by exact application of the corresponding promoted provider. The harness contains no substitute assumption for those evaluation laws. Its log reports exit 0 and axiom lists for all five pairs: the radicand/weight pairs use `[propext, Classical.choice, Quot.sound]`; the divisor/dividend/margin pairs use `[propext]`.

This compilation establishes the exact statement correspondence on the actual copied definitions. It is **not** compilation of the complete modified JonesSyntax and ExecutableJones modules, and in particular does not check the downstream `eval_withInput` proof in its complete original dependency chain. Do not present the 49-line proposed reduction as a fully integrated module build.

**Exact artifact check.** All five provenance file hashes recompute correctly. Independently generated source diffs match `structural/jones.patch` byte for byte. `JonesSyntax` is 179→179 physical lines; `ExecutableJones` is 300→251, a net reduction of 49, counting the extra line for qualified names. The machine-readable checks are in `audit/jones-review-checks.json`.

## 9. Incoming-directory scope confirmation

At the pinned source, the current `docs/incoming` tree contains only its README. The opening table retires the 22 DiophantineConsistency proof packets into the requested a–v research directory. Other Lean-simplification entries concern K215: phase15 transfinite recursion, quotient syntax, PowerSets and dense bridges, or historical packets retired to `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals`, with reconciliations under `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels`.

The entire current README was searched and the relevant retirement/checkpoint summaries read. They do not advertise the present Jones bridges, thirteen-carrier norm/transport estimates, helical diagonal pullback, monomial-list interpreter or function-valued composition tails. No claim is made to have downloaded historical retired binary archives or recursively audited every unrelated manuscript linked from that README. The novelty claim is against the present contents of the two requested directories and the 22 identified Diophantine proof packets, with this scope made explicit.

## 10. Thirteen-carrier norm gap and affine carrier step

**Mathematics: PASS.** For the auxiliary norm, set `D=S²−1`. From `S≥2`, `D≥3` and `3S²−4≥0`. The maintained norm equation yields the exact identity

`D*(4V²−y²) = (3S²−4)*V² + 1`.

Its right side is strictly positive, so `4V²−y²>0`. The existing absolute-square comparison theorem yields `|y|<2|V|`. This avoids the two contradiction/product constructions in the former bound tail. The new patch **retains the entire existing `y≠0` prefix, including its V-nonzero argument, verbatim**. It therefore does not claim credit for earlier integer-unit simplification ideas, nor should its report say the complete patched theorem removes that prefix.

For the shared carrier step, set `A=4*(1+b*V²)`. The new helper proves `A>2|V|+1` under the unchanged integer premise `b>0`. The proof supplies the nonnegative product `(b−1)V²` and square `(2|V|−1)²`; these are sufficient for the final polynomial inequality, for every integer V including zero and negative V.

Soundness rewrites the carrier equation as `y=1+4bm−AG`. If G were negative, integer discreteness gives `G≤−1`, so y lies strictly above the allowed band `|y|<2|V|`. The candidate uses `y≤|y|` for the contradiction and retains both positivity premises on b and m.

Completeness retains the **same explicit witness** as before. Given `G=bg` and `y−1=4be`, it sets `m=e+(1+bV²)g`. It then uses `4bm=y−1+AG`, `G≥1`, `V>0`, `y>−2V`, and `A>2V+1` to get `4bm>0`, hence `m>0`. The former separate proof that g is positive and several repeated scale estimates disappear. The final revision also uses the same normalized equation to close the final carrier equality instead of expanding the witness again. The witness expression and final affine carrier equation are unchanged.

**Statements/data and imports: PASS.** The three existing theorem statements are unchanged. All executable/core definitions and parameter ordering remain untouched. The only new production declaration is `ThirteenCarrierSoundness.carrier_step_dominates`. `ThirteenFreshSeed` already imports its provider, so there is no new import or import-cycle issue. Existing positivity, divisibility, signed-coordinate and exact-equality premises all remain.

**Novelty: PASS in the two specific obligations.** The norm-gap identity is not earlier fundamental-unit minimality, nonsquare norm descent, or Pell sequence ratio analysis. The affine-step comparison supplies a single bound used in both positive-carrier completeness and transport soundness; neither target occurs in earlier proposals. The two mechanisms may share a report chapter, but should not be conflated: one bounds norm roots and the other controls their affine encoding.

**Evidence scope and artifact binding.** The exact three replacement theorem blocks and helper compile in `AlgebraCandidates.lean`; `algebra_compile_result.json` records exit 0 at Lean 4.32.0 and the matching source hash. The standalone output prints only standard axiom sets. Complete modified source files are provided as overlays; those two complete modules and their downstream clients were not rebuilt in this scope. Both old/new file hashes recompute correctly and independently regenerating the unified diff yields a byte-for-byte match with `algebra_ideas.patch`. Each candidate theorem block equals the compiled harness block after normalizing the helper namespace qualification; the helper itself is byte-identical. The final harness SHA-256 agrees with the successful compiler receipt. These bindings were rechecked after the final three-line reduction in `carrier_exists`.

The combined source is 290+217→286+205 lines: **16 physical lines removed**, including helper documentation and spacing. The norm-gap tail saves five lines; the two carrier clients together save seventeen while the helper plus comment/separation costs six. The soundness file grows by 12 bytes despite losing four physical lines; source-line reduction and byte reduction should not be confused.

## 11. Final Syntax reconciliation and combined scope

The final SyntaxCoefficients patch regenerates byte for byte from its baseline and candidate files. The exact SHA-256 values agree with `syntax/metrics.json`; the 120→111 line count is correct. The persisted baseline receipt explicitly states that it was reconstructed verbatim from observed compiler output after an ENOSPC failure; both baseline and candidate endpoint axiom sets are the same three standard axioms. This is a transparent evidence note, not a failed Lean check.

Across the reviewed eight-file proposal set, physical-source savings total 94 lines: 49 Jones, 16 carrier, 9 SyntaxCoefficients, 10 helical and 10 composition. **Only 19 of those lines belong to three complete-module-compiled edits.** The remaining 75 are supported by exact theorem/extracted-definition kernels and static complete-module patches. These are pinned-source accounting figures, not guaranteed additional counts after every competing prior proposal is physically merged, and they establish no runtime or elaboration speedup.

Final review: the six precise proposed mechanisms pass mathematical/source review and scoped novelty screening; the coprime-divisibility cleanup is excluded as a repeat. All reviewed patch/hash mismatches were resolved. No new axiom declarations, theorem assumptions or polynomial construction changes were introduced in the reviewed scope. The inspected compiler outputs report only standard Lean axioms; old/new axiom-set equality is specifically checked for the composition records and the SyntaxCoefficients endpoint. No all-endpoint replay claim is made.
