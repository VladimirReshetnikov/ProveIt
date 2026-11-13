# Captured-provider replay of the canonical P65 iPRA endpoint

The merged source `Lean/DiophantineConsistency/Compact44/IPRAPositive65.lean`
and its 29 missing dependencies were compiled with Lean 4.32.0 against the
captured reverse-provider overlay documented in `research/p65-reverse-provider/`.
The four endpoint declarations `positiveBridge`, `native_equivalence`,
`standard_equivalence`, and `reference_equivalence` all compile with Lean
axioms `[propext, Classical.choice, Quot.sound]`. The latter three assert
provability in the respective encoded iPRA theories of equivalences between
the positive-shifted graph's no-zero formula and the negation of the selected
mapped Foundation ZFC refutation predicate. The exact statements are in the
pinned endpoint source. The result concerns this Lean graph and selected
consistency formalization; correspondence to any external rendering is a
separate obligation.

This is a **captured-provider replay**, not a clean build of all current
canonical sources. All 30 compiled files are byte-identical to their
canonical sources except for the import substitutions pinned in the manifest.
In particular, canonical `P65Graph` imports are mapped to the same previously
checked `P65GraphShim` module and object used by the reverse direction; the
shared graph declaration is not duplicated. The graph shim's body is compared
with canonical source by the separate checker in
`research/p65-halt-converse-algebra/`. The imported reverse-provider objects
are hash-pinned but their full transitive source/object ancestry remains
unauthenticated. Their qualified build evidence is in the reverse-provider
packet. This check does not remove that limitation.

After this replay, origin commit `e1b79c42eb` changed the current
`Compact44/P72Exact.lean` and `Compact44/P72Power.lean` sources used by the
reverse-provider overlay. This recorded endpoint replay therefore concerns the
earlier hash-pinned versions; see the reverse-provider record for the hashes.
A later [post-merge replay](../p65-post-merge-replay/README.md) forcibly
recompiled the affected closure visible in the recorded manifests through
`IPRAPositive65`. It retains the captured-provider and unauthenticated
transitive-ancestry limitations, and is not a clean current-source rebuild.

`manifest.json` records the 30 canonical source hashes, generated shim
hashes and exact import substitutions, plus the hashes of 24 selected
captured direct-import objects. `results.json` records all 30 final object
and compiler-log hashes. Objects remain under `/tmp` and are not committed.
The compiler logs all record exit 0; no warnings, source placeholders,
`sorryAx`, or unexpected printed axioms were found by the audit. The audit
reads multiline Lean axiom lists as well as single-line lists. The cached
replay exited 0 and verifies hashes of the existing objects; it is not a
second compilation. `manifest-check.txt`, `audit-result.txt`,
`cached-replay.txt`, and the individual logs record these checks.

The preparation and build scripts are specific to the recorded workspace
and `/tmp` provider locations. To replay there after the reverse-provider
packet and the graph shim have been built, run:

```sh
cp research/p65-canonical-endpoint-provider/prepare.py /tmp/p65_prepare_canonical_endpoint.py
cp research/p65-canonical-endpoint-provider/build.py /tmp/p65_build_canonical_endpoint.py
cp research/p65-canonical-endpoint-provider/check-manifest.py /tmp/p65_check_canonical_endpoint_manifest.py
cp research/p65-canonical-endpoint-provider/audit.py /tmp/p65_audit_canonical_endpoint.py
python3 /tmp/p65_prepare_canonical_endpoint.py
mkdir -p /tmp/p65-canonical-endpoint-provider/lib
cp -asn /tmp/p65-reverse-provider/lib/. /tmp/p65-canonical-endpoint-provider/lib/
python3 /tmp/p65_check_canonical_endpoint_manifest.py
python3 -u /tmp/p65_build_canonical_endpoint.py
python3 /tmp/p65_audit_canonical_endpoint.py
```

The builder uses `-M6000`, `-j1`, and a 300-second timeout per module;
it checks the pinned source/import bindings before compiling, stops on a
failure, records compiler commands and output, and validates shim and
object hashes before reusing a cached object. The earlier reverse-provider
build used one documented 6 GB retry and has one retained benign linter
warning; neither is part of the 30-module successful log set here.

```text
manifest.json        bb0488e85aa2d8a2c3ba6943cddcb208a1b1e9704913ec6ba6d2cc82e3894a00
results.json         4c19cd870cce5cb41e12be93f0b0ddc3b3eca4010bdf6e86a737db2c0cfe7044
prepare.py           adede05494d3078b69fcf39e2348e623b56a7ca5e92096c379f071bd4763121b
build.py             d18f6d6fc161c324f4d58b4000fd5860db1bb9a091365ff03ee5c837172ab2ec
check-manifest.py    5ca7bfd62c3583098210f8a8c6eea739a87fa141258ff514cf3848a59b2695e4
audit.py             870893dcd27a8dfac953c83a2c666e22e2f3e004a1cae5ea692f9d9077c2d19e
IPRAPositive65.lean  675eafadc49f1248e80a965d834b702d073eafda4c0aff5f0cc84f1fb1c9d7f1
IPRAPositive65.olean 67ee78d4c54c3bd0baa2b3734a4d11a70d3b199557839b08b4faa1cad1adfb19
```
