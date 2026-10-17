# Binding one internal free-variable label

`ModelCodedBindOne` supplies a total represented syntax operation in every model of IΣ1. At current binder depth d it replaces only free label a with bound label d. It preserves existing bound labels and every other free label. Beneath either quantifier the depth increases by one while a stays fixed. The chosen label, depth, formulas, terms and argument-vector lengths may all be nonstandard elements of the arithmetic model.

The fixed Σ1 graphs are defined before the model. Term recursion has the two parameters (a,d); formula recursion carries their encoded pair and changes only d at a binder. Totality on arbitrary raw inputs comes from the existing represented structural-recursion machinery. Well-formedness is a separate theorem about well-formed inputs.

For every internally well-formed level-d formula p, the checked conclusions are

```text
IsSemiformula L (d+1) (bindOneAt L a d p)
subst L (qVecIter L d (&a ∷ 0)) (bindOneAt L a d p) = p.
```

The opening vector preserves every old bound slot below d and sends the new slot d to free label a. The term and formula inductions quantify internally over a; the formula induction also varies d under quantifiers. In the binder case, the existing `qVecIter_succ` equation gives exactly the lifted opening vector. Thus no external finite arity, standard-code condition or shift-fixedness assumption is used.

`namedAll L a p` is the actual universal constructor applied to `bindOneAt L a 0 p`. It is an internally well-formed formula whenever p is, and opening its bound body at free label a returns exactly p. This is intended as the named-binder syntax needed by a future internal decoder for C254's `wal a h`.

Other free labels remain free, so the output is generally **not shift-fixed**. The module does not claim it is. It also does not transform a proof of p into a proof of `namedAll L a p`: the GEN proof-translation obligation needs its own internal renaming or compiler argument. No numeric decoder, arithmetic consistency comparison or machine-state claim follows from this checkpoint alone.

## Verification

The final 351-line source and 56-line audit pass pinned Lean 4.32.0 with **15 named axiom reports and 19 callers**, standard three axioms only and zero warnings. Source and audit take 13.416 s and 2.599 s. The check uses `-M4096` and one thread, reusing nine source-matched local objects, six traversed external boundaries and the actual first Omega object. All 40 input paths and the fresh object are checked afterward. The prior complete Foundation namespace mirror is a resolution boundary; no whole-cache freshness is asserted. No dependency is rebuilt, fetched or changed.

Runs 1–3 failed on graph elaboration: an implicit language argument, typed versus untyped vector record shapes, a quasiquote projection and normalization of the five-entry graph argument vector. The final source uses a separately named raw formula graph and the exact vector-composition lemma. The main theorem statements and opening-inverse architecture are unchanged. Failed source snapshots and diagnostics remain separate from the successful run.

The portable checker freezes the final source/audit bytes and the 15/19 contract. It checks compiler and dependency identities, current selected source/object continuity, actual first providers, direct tool imports plus Omega, and all post-build hashes. Original-path and relocated-cache preflights are explicitly unbuilt. Four controls reject Python `-O`, nonempty output, a fake first Omega object and a changed isolated predecessor object; that copy is restored afterward.

## Reproduction

```sh
python -B Logic/Interpretability/ZFCinPA/check_model_coded_bind_one.py \
  --dependency-root /path/to/dependency-checkout \
  --specialization-evidence /path/to/specialization/verification.json \
  --output /fresh/external/bind-one
```

Source, audit and predecessor evidence default to maintained files. `--source` and `--audit` accept relocated copies of the same frozen bytes. `--specialization-cache` selects a consolidated cache containing the nine predecessor local objects, and `--namespace-cache` selects a cache root with the complete Foundation namespace mirror. The predecessor record's existing paths are otherwise used. Repeated `--library-path` options choose existing library directories in order. `--prepare-only` invokes no proof compiler.
