# Specializing an internal number of universal binders

`ModelCodedSpecialization` now supplies a total represented proof-code operation in every model of IΣ1. Given an actual internal proof of `qqAlls body m`, it returns an actual proof of `subst L (fvarVec m) body` for every internal binder count `m` and every internally well-formed level-`m` body. The count, formula and proof code may all be nonstandard. This removes the repeated-specialization obligation left by the preceding [free-parameter closing construction](model_coded_free_closure.md).

The operation is uniform in a fixed encodable, LOR-definable language and in the fixed Δ1 theory whose proof relation is used. It does not interpret one language in another. It adds no theory axioms and assumes no set-theory model.

The single-step constructor uses literal codes for weakening, propositional excluded middle, existential introduction and cut. Given a proof of `∀body` and a term `t`, it constructs a proof of `body[t]`. It does not select a proof from an assumed existential derivability assertion.

A total raw state is `⟪remaining,currentFormula,currentProof⟫`. At remaining 0 the step retains the state. Otherwise it removes one remaining binder, extracts the current formula's body with the actual `sndIdx`, substitutes the free term `&(remaining-1)`, and applies the literal proof constructor. The same total function is defined on malformed states; validity is a theorem about valid inputs, not a test or oracle used by the operation. A fixed Σ1 primitive-recursion graph iterates this step.

The main induction is Π1:

```text
∀ body proof,
  IsSemiformula L m body → Proof T proof (qqAlls body m) →
  Proof T (specializedProofCode L m body proof)
    (subst L (fvarVec m) body).
```

Both proof predicates are Δ1 and the output operation has a total Δ1 graph. This permits IΣ1 induction with changed formula and proof inputs. An implication between two existential provability assertions would not provide the same induction predicate.

A generic represented `qVecIter` pushes substitution under an internal number of quantifiers. In the successor case, the first elimination changes the body to

`body' = subst L (qVecIter L m (&m ∷ 0)) body`.

The induction hypothesis applies to the resulting proof of `qqAlls body' m`. Existing substitution composition and the checked vector identity

`termSubstVec L (m+1) (fvarVec m) (qVecIter L m (&m ∷ 0)) = fvarVec (m+1)`

identify its output formula with the required simultaneous opening. All vector-index reasoning uses internal inequalities and zero/successor decomposition. No external finite enumeration of indices is used.

The final theorem `openClosedCode_isProof` composes this operation with the checked BindFree inverse. Thus the actual closed Separation/Replacement axiom codes can be specialized to their open schema bodies without a `K.shift = K` premise. Audit callers include unary Separation in ZF and binary Replacement in ZFC, with arbitrary internal free labels on the matrix. The generic theorem also applies to the other two theory/schema combinations.

This checkpoint does not supply a C254/ZFC formula interpretation, translated axiom families for the well-founded/constructible constructions, or the final PA consistency comparison. It does not make a machine-state or runtime claim. The new fixed graphs and all-model correctness are checked, but this module does not separately package their correctness as an actual PA sentence/proof.

## Verification

The final 326-line source and focused audit pass pinned Lean 4.32.0: **14 named axiom reports, 16 callers, standard three axioms only, zero warnings**. The final source check takes 14.047 s and its audit 2.392 s. It uses `-M4096` and `LEAN_NUM_THREADS=1`.

Eight source-matched local objects and six traversed external boundaries are reused, together with the actual first Omega toolchain provider. Thirty-eight input paths and the fresh object are checked before/after. A complete prior Foundation namespace mirror resolves the cached boundaries; no entire-cache freshness is asserted. No dependency is built, fetched or changed.

Runs 1 and 2 failed on elaboration details: recurrence rewrite orientation, internal-model numeral inference, HFS empty-set normalization, a tactic-layout parse error, and the missing total-step Δ1 function instance. Run 3 passes after those corrections. The theorem statements and induction architecture are retained. The first-draft-to-final diff and failed records remain distinct from the successful evidence.

The portable checker freezes the final source/audit hashes, exact 14/16 audit, compiler and dependency pins, current selected source/object continuity, actual first providers and direct toolchain imports plus Omega. Source and provider relocation preflights are explicitly unbuilt. Python `-O`, nonempty output, a fake first Omega object and a wrong copied predecessor object are rejected; the isolated copied object is restored afterward. No proof replay is performed for those controls.

## Reproduction

From the repository root, using existing checked closed-schema prerequisite objects:

```sh
python -B Logic/Interpretability/ZFCinPA/check_model_coded_specialization.py \
  --dependency-root /path/to/dependency-checkout \
  --closed-evidence /path/to/closed-schema/verification.json \
  --output /fresh/external/specialization
```

Source and audit default to maintained files. `--source` and `--audit` accept relocated copies of the same frozen bytes. `--closed-cache` optionally selects a consolidated cache containing the eight predecessor local objects; `--namespace-cache` selects a cache root containing its complete Foundation namespace mirror. Without overrides, the successful predecessor record identifies these objects and mirror. `--prepare-only` performs no proof compilation; repeated `--library-path` arguments choose existing library directories in order.
