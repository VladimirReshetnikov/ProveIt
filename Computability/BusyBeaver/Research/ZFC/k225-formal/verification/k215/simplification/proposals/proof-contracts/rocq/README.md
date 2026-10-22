# One truth-free derivation for the Lean and Rocq implication cores

This package ports the **current 58-step Lean derivation** to a representation-independent
Rocq module and reconnects the existing numerical API. It is an implementation of the
repository's existing derivation, not a claim of a newly discovered implication proof.

Baseline: ProveIt `6f0d42d368506bc29c70ace1c992ed88b2651346`.
The input is the unchanged `k225-formal/rho8cd/derivation_core.txt`; its SHA-256 is
`f0a2e60d3574615aefa8ce987e783b69a89dd95516dc7238caa569b4a938f116`.

## What changes

`generator/generate_domrho8_cd.py` adds the `--core-rocq` rendering mode beside the
existing `--core` Lean mode. Both render exactly the same neutral derivation.
The existing Lean core and both older Nat renderings are reproduced byte for byte.
The untrusted renderer recomputes the explicit instantiations; the kernels check
the emitted proof terms independently.

`coq/DominatedImplication.v` proves the unrestricted Lukasiewicz row, composition,
and antecedent prefixing for an arbitrary type `A`, binary connective `wim`, and
relation `below`. Its hypotheses are precisely:

1. `below a a`;
2. `below u x -> below u (wim x y)`;
3. `below u y -> below u (wim x y)`;
4. closure of the predicate `T` under modus ponens;
5. the row `((c -> u) -> a) -> ((a -> c) -> (b -> c))` whenever `below u a`.

There is no truth constant, formula parser, injectivity hypothesis, transitivity
hypothesis, or arithmetic code in this generic proof. These are universally
quantified parameters in the theorem type, not global axioms.

`coq/DomRho8.v` instantiates this module with the exact inherited numerical `wim`
and natural-number order. It preserves the public `DomImp` record, its three
projections, and the signature of `rho8_all`. The record retains its truth field
for API compatibility; the implementation does not use that field. The additional
`rho8_all_of_restricted` explicitly exposes the weaker, truth-free interface.
`composition` and `lift_right` mirror the Lean core's public consequences.

The new proof applies to **all natural-number codes**, including codes that a
prospective formula decoder would reject. It therefore avoids introducing a
well-formedness premise into the existing calculus-equivalence theorem.

## Measured source change

| Source included in comparison | Lines | UTF-8 bytes |
| --- | ---: | ---: |
| Baseline production `DomRho8.v` | 1,169 | 22,673 |
| New generic core | 275 | 13,640 |
| New numerical adapter | 54 | 1,998 |
| New core and adapter together | 329 | 15,638 |
| Reduction | 840 (71.9%) | 7,035 (31.0%) |

The comparison includes both new proof modules, so it does not hide moved proof
text. The renderer grows by adding a second target language. The 52-step
Nat-specific Rocq proposal already in `rho8cd/` is shorter in bytes than this
generic core plus adapter; the purpose here is one common truth-free specification
for both proof assistants and reuse across numerical encodings, rather than a
claim that this is the shortest possible Rocq source.

## Reproduction

```sh
python3 build.py --coqc /path/to/coqc --coqchk /path/to/coqchk --out /tmp/k215-core-check
```

The script acquires the shared `proveit-k215-proof-build.lock`, uses a fresh source
directory, compiles the new generic module and adapter, and compiles the unchanged
production `Codes222.v`, `Thm222.v`, and `ThmDom.v` against them. It additionally
compiles the original production `DomRho8.v` in a separate namespace for a local
comparison. It recursively checks `K215F.ThmDom` with the compiler's matching
`coqchk`. No compiled object is supplied by this package.

The accepted local check used **Coq 8.18.0 / OCaml 4.14.1**. Its five `Stdlib`
namespace wrappers simply re-export the installed Coq standard modules; the
inherited proof sources are not edited. On Rocq 9, the script uses its installed
`Stdlib` directly and does not compile these wrappers. The exact inherited
numeric sources match the pinned K230 manifest hashes. The unchanged client
`ThmDom.v` is byte-identical to the ProveIt baseline. See `provenance.json` and
`evidence/verification.json` for bindings, commands, timings, and log hashes.

The generic theorems, all four adapter theorems, and `thmDom_iff` print
`Closed under the global context`. The recursive kernel context summary lists
no axioms, type-in-type dependencies, unsafe fixpoints, or assumed positivity.

**Scope:** this is a checked isolated core and client migration. It is not a fresh
Rocq 9.1.0/stdlib 9.0.0 build of the 215-state machine endpoint. It does not replace
the repository's accepted full-build receipts, prove consistency of ZFC, or supply
an internal PA or serialized ZFC proof.

## Production integration

`proof-sources.patch` contains the three proof/generator changes against the
pinned baseline. It is a source patch, not a completed production-manifest migration.
To integrate the checked idea:

1. Add `DominatedImplication` immediately before `DomRho8` in the 215 variant's
   compile order, and include the new source hash in the extension manifest.
2. Change the `DomRho8` branch of `rocq/rocq-extension/regenerate215.py` to invoke
   the shared renderer on `derivation_core.txt` with `--core-rocq`; preserve the
   numerical adapter as a small template and copy it to the generated tree.
3. Regenerate and refresh the source/manifest/regeneration hashes. Keep the exact
   numerical formula definitions and machine table fixed.
4. Use the maintained Rocq 9.1.0 driver and shared lock to rebuild the complete
   K215 closure, both sparse/dense endpoint clients, and recursive `coqchk`.
   Accept the migration only after the endpoint assumption reports and exact
   imported-object bindings pass.

The existing Lean `--core` output needs no proof change. Sharing the neutral
derivation reduces maintenance drift while preserving two independent kernel
checks. A later change to the derivation can regenerate both cores in one
operation and compare their public statements before either enters production.

## Files

- `coq/`: proposed production proof modules.
- `generator/`: extended renderer and unchanged neutral derivations.
- `reference/`: byte-identical minimal dependencies, original proof/renderer,
  current Lean core, and Coq 8 namespace shims.
- `evidence/`: accepted isolated-build receipt and raw logs.
- `provenance.json`: exact source pins and digest comparisons.
- `licenses/`: project license and inherited attribution notices.

The preexisting offset-certificate mirror proposals and normalized source-checker
work remain separate. This package does not repackage those results as new work.
