# Shared abstract implication proof: a checked Rocq implementation

Repository reviewed: `VladimirReshetnikov/ProveIt`, commit
`2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`.

## Result and attribution

The production Lean proof already has a 58-step, truth-free condensed-detachment
derivation in `DominatedImplication.lean`. Its exact mathematical derivation is
**inherited** from `k225-formal/rho8cd/derivation_core.txt`; this packet does not
claim to discover it or shorten its step count. At the reviewed commit the
production Rocq `coq/215/DomRho8.v` still uses a 735-instruction reflective replay,
even though shorter Rocq renderings are present as research proposals.

This contribution supplies a **new Rocq backend for the same abstract 58-step
proof**, plus a small natural-code adapter preserving the production `DomImp`
record and `rho8_all` API. The unchanged `ThmDom.v` client compiles against it.
Consequently both assistants can share the same proof input and maintain only
small representation-specific adapters. The existing Lean renderer reproduces
the production Lean core byte for byte; this check is recorded in provenance.

The new backend reuses the upstream parser, unifier, and instance reconstruction
unchanged in `upstream_generate_domrho8_cd.py`. The backend is untrusted: each
generated lemma is an explicit application of modus ponens to explicit premise
instances, and the proof assistant checks every such term.

The previous `proof-core` proposal already contained a longer abstract Rocq
proof. Our delta is a checked port of the current compact derivation and its
tested production numerical adapter, not the invention of abstraction or of
condensed detachment.

The proof-source comparison includes the generic module **and** the adapter:

| Proof source | Lines | Bytes |
| --- | ---: | ---: |
| Production reflective `DomRho8.v` | 1,169 | 22,673 |
| New shared abstract core | 281 | 14,252 |
| New natural-code adapter | 36 | 1,374 |
| New total | 317 | 15,626 |

That is 72.88% fewer source lines and 31.08% fewer bytes for this proof slice.
It is not a reduction percentage for the whole correctness proof. Generator
and archived-input sizes are separate; generated certificate line counts and
explicit proof-term line counts are different presentation formats.

There is also an **already supplied 52-step numerical Rocq rendering** from
`rho8cd/derivation.txt`, measuring 11,190 bytes. Our 15,626-byte core-plus-adapter
is **not the smallest available proposal by source bytes**. The 52-step option
is preferable if minimizing this isolated numerical proof is the only goal.
The shared-core option earns its extra bytes by matching the maintained Lean
abstraction, avoiding a truth premise in the core, and supplying composition
and lifting as well as rho8. Its value is one shared mathematical proof with
small representation adapters. The inherited 52-step proposal was regenerated
for a size/hash comparison here; it was not compiled in this packet's fresh
verification slice. See upstream `rho8cd/PROVEIT_STATUS.md` for its separate
adoption and verification status.

## Mathematical interface

Let `A` be any type, let `imp : A -> A -> A`, and let `below` be a relation with
reflexivity and the two closure rules

```
below u x -> below u (imp x y)
below u y -> below u (imp x y).
```

No transitivity, antisymmetry, injectivity, decoder, natural-number encoding,
truth constant, bottom element, or normalization equation is assumed. For any
predicate `T : A -> Prop`, assume modus ponens and just the restricted rows

```
below u a -> T (imp (imp (imp c u) a) (imp (imp a c) (imp b c))).
```

`DominatedImplication58.v` proves all unrestricted rows, composition, prefixing,
and lifting of an already proved implication. The 58 derivation steps share
one proof DAG. Its dependency slices contain 52 steps for unrestricted rho8,
52 for composition, and 50 for prefixing; those are measurements of the
inherited DAG, not lower bounds or new search results.

In the actual code algebra, `imp x y = 4 * P x y` and `below` is natural order.
The adapter obtains both growth rules from `P_ge_l`, `P_ge_r`, transitivity of
natural order, and `P x y <= 4 * P x y`. That last inequality is a direct
instance of `Nat.le_add_r`, so the adapter uses no arithmetic automation.
The `dtruth : T 0` field is retained for compatibility and is not used by the
new derivation. The generic theorem states the genuinely weaker assumptions.

## Checked boundary

The supplied verification script freshly compiles:

1. The exact archived `K230S.KCode230` and `K230L.Codes230` dependencies.
2. The production `K215F.Codes222` and `K215F.Thm222` sources.
3. The new abstract core and the new `K215F.DomRho8` adapter.
4. The unchanged production `K215F.ThmDom` client.

The local toolchain is **Coq 8.18.0 / OCaml 4.14.1**. Private compilation copies
change only `From Stdlib Require` to `From Coq Require`; original input bytes,
compiled bytes, objects, logs, and their hashes are recorded separately.
The two archived coding dependencies are recovered from the production
`verification/k215/rocq/actual/evidence.tar.gz` source snapshots, with their
original CRLF line endings preserved in this packet.

All four generic theorem reports, the numerical `rho8_all`, and the actual
`thmDom_iff` report a closed global context. Recursive `coqchk` of
`K215F.ThmDom` reports no axioms, unsafe fixpoints, or assumed positivity.

**This is a checked seven-module calculus slice.** It is not a fresh build of
the complete 215-state binary-machine/ZFC endpoint, and it is not a claim of a
Rocq 9.1 production replay. Those remain integration gates. The Turing-machine
table, initialization, runtime simulation, and consistency calibration are
unchanged and outside this new check.

`CheckTypes.v` also typechecks the exact old numerical `rho8_all` signature
against the new proof and prints the generic and numerical theorem types.
The raw reports are included in `evidence/`; the API probe is additional to
the seven library modules, not an additional assumption in their closure.

## Reproduce

With `coqc` and its matching `coqchk` on PATH:

```sh
python3 generate_rocq_core.py --out /tmp/DominatedImplication58.v
cmp DominatedImplication58.v /tmp/DominatedImplication58.v
python3 verify_rocq.py --out /tmp/k215-abstract-rho8-check
```

Use a fresh, empty output directory. Add `--baseline` to compile and audit the
old reflective replay in a separate namespace tree as a local comparison.
Use `--coqc` and `--coqchk` to select a matched alternative toolchain.
The script checks closure through `ThmDom` and exact regeneration, and records
source/object hashes and measurements. No downloaded binaries are included.

## Production integration

The source-only patch adds `coq/215/DominatedImplication58.v` and replaces
`coq/215/DomRho8.v`; `ThmDom.v` needs no mathematical change. Before promotion:

1. Add the backend to the maintained `rho8cd` generator, keeping
   `derivation_core.txt` as the shared input.
2. Change `regenerate215.py` to emit the core and adapter instead of calling
   `generate_domrho8_rocq_compact.py` for the old certificate replay.
3. Put the new generic module immediately before `DomRho8` in compile order,
   update source manifests and regeneration receipts, and rerun regeneration.
4. Run the production Rocq 9.1.0 / rocq-stdlib 9.0.0 build and recursive
   `coqchk` of both exact sparse/dense endpoint clients.

If the generic module is shared between K215 and K217, put it in a common
logical namespace rather than generating duplicate proof bodies. That wider
reorganization is a proposal; this packet deliberately checks the K215 client.
Hashes establish byte identity and build provenance, not mathematical soundness;
the kernel-checked proof terms supply the latter.
