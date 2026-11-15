# PA194 site-10 path to literal halt

`PA194HaltPathSegment.path10` kernel-checks the actual pinned source-program path 10 as `[false,false,true]`. `haltPathSegment` uses the existing all-model literal row/three-step proof to show that a state-24 packed physical frame with that path followed by an arbitrary model-valued suffix reaches packed literal control 194 after exactly three steps; the left tape is also arbitrary. The proof uses the actual path word, not a separately postulated bit pattern.

`codeHitReachesLiteralHalt` composes this segment with generic gated first-hit extraction. In any candidate PRA model whose arithmetic reduct satisfies IΣ₁, a nonzero arbitrary PR code hit yields a bounded source index whose corresponding physical clock plus 3 reaches a state with control at least 194, assuming the stated synchronization, clock bound, and that hit frames have the site-10 path. Non-hit frames need not have that path. `PA194SourceHaltSite.uniqueHaltLeaf` is a separately checked certificate identifying this path as the only explicit source halt leaf; it is not imported by this module. Identifying the arbitrary code hit with a source-site hit, proving the conditional frame property and synchronization, and relating source sites to the higher-level scheduler remain open. This is a Lean model theorem, not an object-iPRA proof or an unconditional machine/Con(PA) direction.

Run from the repository root:

```
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-halt-path-segment.sh "$PWD" Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-unified-coherent/build /dev/shm/pa194-termgraph /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

The checker pins selected source and dependency objects, rejects inherited Git overrides, and compiles the generic gated chain, two repository literal-row/controller modules, and this module together in a fresh output, with axiom audits. The baseline, code-graph overlay, and general project and package foundations remain prebuilt; named hashes and a baseline manifest do not authenticate their full transitive closure or cross-overlay compatibility. This is a staged replay, not a self-contained source build.
