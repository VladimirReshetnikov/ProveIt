# Read-only fixed-85 source-selection plan with Omega repair

This packet is a **lexical source-selection plan**, not an overlay, source
copy, build plan authenticated against compiled providers, or Lean proof. It
selects the 1,354 sources from the pinned fixed-85 lexical manifest, with
exactly one explicit mapping change:

```
logical module: ResidueSignFreePower
selected bytes: research/ordinary13-signfree-omega-repair-draft/ResidueSignFreePowerRepaired.lean.src
excluded old:   research/ordinary13-residue-signfree-power-model-draft/ResidueSignFreePower.lean.src
```

The selected replacement retains the original logical namespace and theorem
signatures. Its **basename is not the logical module name**. The plan records
that mapping; it does not make Lean resolve the altered import and does not
copy or rename any source. A future isolated provider arrangement must choose
one source for each logical module and ensure the original or another
conflicting `ResidueSignFreePower` source/object is not selected alongside the
repair. Identical source bytes alone do not authenticate a compiled object.
No source, compiled object, search path or existing evidence is changed here.

`selection.json` pins each selected source path, hash and lexical imports,
the local dependency-first order, the replacement's old/new import lists,
and the 38 reverse-reachable local modules. The checker re-reads and hashes
all 1,354 source files, checks their actual lexical import lines and verifies
the same local reachability and dependency order. The old direct
`Mathlib.Tactic.Omega` frontier edge is gone; the replacement adds imports of
`Mathlib.Tactic.NormNum` and `Mathlib.Tactic.Ring`, both already present in
the prior frontier, leaving 93 **external/unresolved-to-this-lexical-scan**
names. These names are not claimed absent from disk: the separate frontier
inventory locates many current source files. Conversely, presence does not
select, compile or authenticate them.

The one-source collision policy is a requirement for a future plan, not an
assertion that the present global filesystem or Lean search path has been
surveyed. This packet does not scan the imports of the 93 external frontier
sources, choose Mathlib/Foundation/toolchain or compiled package providers,
resolve dynamic-library/object collisions, reproduce historical ancestry,
reserve disk space, run Lean, inspect axioms, or establish the fixed-85
iPRA endpoint. The 38-module affected order is only the reverse closure inside
the pinned local lexical graph; other consumers and external dependencies
may exist.

From `Computability/DiophantineConsistency`, run the **read-only** default:

```
python3 -I -S -B research/ordinary13-fixed85-signfree-source-selection-plan/generate.py | cmp - research/ordinary13-fixed85-signfree-source-selection-plan/receipt.json
```

The optional `--write` switch regenerates only this packet's `selection.json`;
it does not copy or mutate any selected source.
