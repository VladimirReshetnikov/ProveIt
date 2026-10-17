# Explicit proofs of open Separation and Replacement instances

`ModelCodedOpenSchemaAxioms` constructs actual represented ZF and ZFC proof codes for `sepBody K` and `repBody K`. The unary or binary matrix `K` is an arbitrary internal formula in a model of IΣ1, including nonstandard codes and arbitrary internal free labels. There is no `K.shift = K` premise.

The one total raw operation is

```text
openAxiomProofCode L p =
  specializedProofCode L (bv L (bindFreeAt L 0 p)) (bindFreeAt L 0 p)
    (axiomCode (closeFormulaCode L p)).
```

Its fixed Σ1 graph is chosen before the arithmetic model. The operation exists on every raw input. Its correctness requires an internally well-formed formula and membership of its particular closed code in the fixed Δ1 theory. The checked closing construction supplies that membership for the actual Separation and Replacement recognizers, and the checked specialization iteration opens every binder again. Thus the four `*_isProof` theorems concern actual ZF/ZFC proof predicates, rather than additional axioms or assumed schema closure.

The four typed proof carriers retain exactly this literal raw proof code. `typedProofOfCode` merely constructs the carrier from its checked acceptance proof; it chooses no witness. In particular, the result is a proof of an open schema body, not an assertion that the open body itself belongs to the closed axiom class.

These proof constructors discharge the open Separation/Replacement leaves needed by later finite proof templates. They do not yet translate C254 numeric formulas or accepted C254 proofs, supply a syntactic rank/Collection proof template, or establish the PA consistency comparison. The raw code and its fixed graph are explicit; this module does not separately package correctness as a particular arithmetic sentence and its PA proof.

## Verification and reproduction

The final 85-line source and 43-line audit pass pinned Lean 4.32.0 with **11 named axiom reports and 16 callers**, the standard three axioms only, and zero warnings. Source and audit take 3.351 s and 2.563 s, respectively. The check uses `-M4096` and one thread. It reuses nine source-matched local objects, six traversed external boundaries and the actual first Omega provider. All 40 input paths and the fresh object are checked again after the audit. The complete cached Foundation namespace mirror is a resolution boundary, not an assertion of entire-cache freshness. No dependency is rebuilt, fetched or changed.

Runs 1 and 2 failed on explicit singleton normalization, projection unfolding and the typed theory wrapper. Run 3's source passed, while four typed audit definitions required a `noncomputable section`. Run 4 passes with the same source as run 3 and only that audit annotation. Failed records remain separate; none is presented as a successful proof check.

The portable guard freezes source/audit hashes and the exact 11/16 audit, checks the compiler, dependency pins, current selected source/object identities, actual first providers and direct tool imports plus Omega. Original-path and relocated-cache preflights are explicitly unbuilt. Python `-O`, nonempty output, a fake first Omega and a wrong isolated predecessor object are rejected. The copied object is restored after the negative control; predecessor inputs remain unchanged.

```sh
python -B Logic/Interpretability/ZFCinPA/check_model_coded_open_schema_axioms.py \
  --dependency-root /path/to/dependency-checkout \
  --specialization-evidence /path/to/specialization/verification.json \
  --output /fresh/external/open-schema
```

Source, audit and predecessor evidence default to the maintained files. `--source` and `--audit` accept relocated copies of the frozen bytes. `--specialization-cache` optionally supplies all nine predecessor local objects; `--namespace-cache` supplies a cache root with the complete Foundation namespace mirror. Existing predecessor paths are otherwise used. Repeated `--library-path` arguments select existing library roots in order. `--prepare-only` invokes no proof compiler.
