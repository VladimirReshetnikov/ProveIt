# An internal decoder for the literal base4 formula code

`ModelCodedDecoder254` supplies a fixed total Σ1 graph decoding every element of every IΣ1 model into actual Foundation set-language syntax. Codes, variable labels, formula depths and history indices may be nonstandard. The target uses native equality and membership, whose actual set-language symbol codes are 0 and 1.

For a positive source code n, the row obtains tag=n%4 and the two Cantor components a,b of n/4. Tag 0 forms target implication from the two decoded child formulas; tag 1 forms membership on free labels a,b; tag 2 forms checked `namedAll a` of the decoded b child; tag 3 forms native equality. Source code 0 is the literal Code254.T0, membership(0,0) implying itself. Source Cantor pairing remains separate from Foundation's target syntax and HFS encodings.

The course-of-values construction is

```text
H(0)   = seqCons empty T0
H(n+1) = seqCons H(n) (row H(n) (n+1))
D(n)   = znth H(n) n.
```

`seqCons` appends on the right: it inserts the pair (old length,new value). It is distinct from the prepend operation used for target term-argument vectors. The existing all-internal primitive-recursion construction supplies totality. No external well-founded recursion, tree-size budget or fuel cutoff is used.

The checked history is a genuine sequence of length n+1. Its lookup at every i≤n is exactly D(i), and its lookup outside the stored prefix is exactly 0. A positive row's child components are strictly below its source code, by the checked Cantor component bounds and division by 4. A bounded internal prefix induction then proves that every stored value is an actual formula. `decode_succ` exposes the exact positive recurrence with actual child D-values, rather than unresolved history lookups.

The row is also a total function on arbitrary malformed histories. Its formula-validity theorem requires well-formedness of the smaller entries it reads. The generated history discharges that requirement; no input-is-a-standard-code assumption is used.

The checkpoint is syntax, not proof transport. It neither changes nor deletes any of C254's twelve proof rules. Translating those rules, native equality, both bundle inequalities and the a=b matrix branch remains separate. The ordinary-Nat identification with Code254.dec and the literal numeric constructor equations are further interfaces, not assumed by this module.

The zero alias is retained: source wim(0,0)=0, while target implication applied to D0,D0 is a different syntax tree. A proof translator must handle that case by a logical proof/equivalence. Also T0 has free label 0 syntactically, although it is semantically constant truth; later freshness arguments must treat zero explicitly. An alternative decoder could use primitive Verum at zero to simplify that corner, but it would be a separate interpretation revision and would still have the zero implication alias. The current bytes retain literal T0. Generic accepted conclusion n must translate to a proof of D(n); only n=1 plus a separate fixed ZF irreflexivity proof gives target Bottom.

## Verification

The final 245-line source and 71-line focused audit pass pinned Lean 4.32.0: **16 named axiom reports, 24 callers, standard three axioms only, zero new warnings**. Source and audit take 13.938 s and 3.140 s under `-M4096` and one thread.

The exact provider union comprises ten ZFCinPA objects from the passed BindOne closure and eleven native Cantor/core objects, plus six named external boundaries and the actual first Omega provider. The check matches both parent dependency/provider records, all current selected source/object identities, parent audit bytes and actual first providers, then rechecks all 67 inputs and the fresh object. It does not attest an entire dependency cache. The native Cantor record includes its historical compiler version and five style warnings; the current compiler binary is additionally fixed by the passed BindOne digest. No dependency is rebuilt, fetched or changed.

Runs 1–4 fail on API/elaboration details: graph noncomputability annotations, the namespace of the relation-code lemma, local append-lookup wrappers, and native relation quotation/recognizer normalization. Run 5 passes using the exact `isRel_quote_quote` encoder witnesses for equality/membership. The history, decoder semantics and main proof statements are retained. Failed snapshots and diagnostics remain separate.

The portable guard freezes final source/audit hashes and the 16/24 contract. Original-path and relocated 21-object-cache preflights are explicitly unbuilt. Five controls reject Python `-O`, nonempty output, a fake first Omega, a wrong copied BindOne object and a wrong copied native Cantor object. Both isolated copies are restored afterward; original proof inputs remain unchanged.

## Reproduction

```sh
python -B Logic/Interpretability/ZFCinPA/check_model_coded_decoder254.py \
  --dependency-root /path/to/dependency-checkout \
  --bind-one-evidence /path/to/bind-one/verification.json \
  --cantor-evidence /path/to/native-cantor/verification.json \
  --output /fresh/external/decoder
```

Source, audit and both proof records default to maintained paths. `--source` and `--audit` accept copies of the frozen final bytes. `--bind-one-cache` and `--native-cache` optionally provide the two exact local-object groups; `--namespace-cache` provides a cache root containing the complete Foundation namespace mirror. Recorded existing paths are used otherwise. Repeated `--library-path` options select existing library roots in order. `--prepare-only` invokes no proof compiler.
