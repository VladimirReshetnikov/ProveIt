# Exact internal C row in actual ZF

`ModelCodedDecoderContainer254` proves

```text
forall a b c internal, c != a -> c != b ->
  Provable ZF (decode (ArithmeticTemplates254.bundleC a b c)).
```

The arithmetic model is arbitrary IΣ1. All three labels are arbitrary internal
elements, and the two actual bundle gates are the only label restrictions.
The a=b case and valid zero-label cases are included. No external standardness
or bound on an internal label is assumed.

First, finite circuit congruence normalizes the actual numerical C row to
native conjunctions and named existentials. It reuses the checked circuit
decoder, so the relative falsity/implication zero aliases are handled by
provable equivalence under binders. Binder labels retain their original numeric
values. Actual named-GEN is explicit in generic helpers and discharged in ZF.

When a!=b, a finite syntax calculation using the two gates identifies the
native row with an explicit de Bruijn formula. One fixed ordinary one-slot row
matrix has exactly that quoted formula after substitution at free c. The
checked ordinary ZF container theorem is internalized before specialization;
no arbitrary internal matrix is inserted into an external model argument.
Private typed views of bindOneAt/termBindOneAt keep their formation proofs
attached during this finite calculation. Their constructor equations are direct
consequences of already checked raw laws, with exact binder-depth casts. They
add no closure premise or new induction assumption.

When a=b, the repeated name makes the antecedent x in x. A fixed ordinary ZF
irreflexivity proof is quoted and specialized at arbitrary internal a; EFQ and
actual named-GEN prove the universal implication regardless of its consequent.
Named-existential monotonicity combines that proof with a fixed membership
container consequence. The implementation obtains the latter from the checked
power-container witness; ordinary Pairing would also suffice. The other
conjunct may still be captured by the outer existential, as in the actual row.
No freshness premise on that universal theorem is assumed.

The final 330-line source and 16-probe/20-caller audit passed Lean 4.32.0 in
run5 with only propext, Classical.choice and Quot.sound, and zero warnings.
Source/audit times are 5.281986s/2.919505s. Audit callers include arbitrary labels,
the distinct syntax equality, generic GEN signatures and concrete valid triples
(0,1,2), (1,2,0), and (0,0,1); the last exercises coincident a=b. The all-zero
triple fails the actual gates and is not presented as an accepted instance.

The exact guarded union selects 54 project predecessors and six direct external
boundaries from four successful parents: Circuit7/10, LogicalNormalization7/10,
AtomicVacuity10/12, and NativeZF15/15. All four fresh parent objects are actually
imported, shared identities match exactly, and the numeric parents carry only
the previously accepted same-source Cantor pair (bf2 selected, ff1 explicitly
unused). NativeZF adds no Cantor variance. All 141 recorded inputs, actual first
providers, four toolchain anchors, and the fresh object are checked after the
build. Only the selected external source/object boundaries are attested; the
complete supplied Foundation namespace is not independently rebuilt in full.
No dependency build or download occurred.

Portable maintained replay is:

```bash
python Logic/Interpretability/ZFCinPA/check_model_coded_decoder_container254.py --output /tmp/decoder-container-replay
```

The runner supports explicit repository/dependency paths, each parent evidence
and source/audit pair, a selected-project object cache, complete Foundation
namespace cache, compiler and libraries. Explicit library paths replace default
provider discovery, so supply all required existing library roots when using
that option. Packaging adds two unbuilt override/relocated preparations and
four rejection controls: optimized Python, occupied output, changed source,
and a false actual-first Omega object. Preparations query the compiler version
and perform zero proof builds. The portable guard is byte-identical to the
successful executed guard; no successful-proof replay occurred in packaging.

All four unsuccessful attempts, exact sources/audits/guards and repairs are
preserved. The initial parser/symbol-quotation repairs changed no mathematical
statement. The raw finite-alpha simplification reached the default 200,000
heartbeat limit; typed views removed repeated formation-proof search without
raising that limit. The last repair explicitly unfolded typed-view coercions.
The 4GiB/one-thread resource settings were unchanged throughout; no failed sorry
warning was accepted as a checked proof object. Earlier unbuilt normalization
and complete-client plans remain historical in the history record.

This closes the actual C clause. Arbitrary-internal Collection G, full bundle
assembly, general accepted-proof translation and the PA consistency comparison
remain separate. In particular, C contains numeric variable labels, while G
also uses input c as a decoded matrix and needs its own freshness/zero-case
handling. This module does not assert a PA-provable ConZFC equivalence or a
new machine-state count.
