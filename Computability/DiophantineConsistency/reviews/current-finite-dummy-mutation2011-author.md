# Finite actual dummy mutation: author validation

This receipt covers the new `CurrentFiniteDummyMutation2011.lean` and its focused checks. The controller-certificate agent authored and fully read both files before their successful bounded direct Lean compilations. This is author validation, not an independent peer review. The same agent authored the single-position `CurrentDummySafety2011` dependency and several actual word/bound dependencies; the underlying `CurrentDummyMutation2011` was authored by the circuit agent. No frozen prerequisite, shared document or git state was changed for this packet.

## Exact scope

For an arbitrary actual tile assignment `a : ZMod N → Fin 942`, Boolean marker controls, natural whole-cell displacement `s`, and a finite set `S` whose canonical representatives satisfy both `j.val+1<N` and `j.val+s<N`, the module defines the actual Boolean dummy controls `enabled S`. It proves the following ordinary equalities, with the same original zero-dummy word and normalization retained:

```
P(S) = Σ j∈S, (radix^2011)^j.val
Δ(S) = radix^977 * P(S)
C(S) = C(∅) + Δ(S)
F(S) = F(∅) + (K + 2^(47*(2011*s))) * Δ(S).
```

`source_enabled_sum` is independent of Boolean marker bounds and of safety. `exists_finite_normalized_increment` constructs the final bounded normalization from any original actual bounded normalization. Each insertion invokes the existing single-position safety theorem on the intermediate actual Boolean word; it derives nonwrapping from that word's established top bound. No sum bound, desired `F` increment, high-mask premise or modular-target equation is supplied. `finite_normalized_increment` also applies to any independently supplied final actual normalization, by the uniqueness of its strict transport representative modulo `radix^(N*2011)-1`.

`finite_rank_decrement` derives the exact integer rank change

```
R(C(S),F(S)) = R(C(∅),F(∅)) - Γ * P(S),
Γ = rankGamma q (K + 2^(47*(2011*s))) (radix^977).
```

The original `MC`, already source-shifted `MF`, and `J` are retained as arbitrary integer ports. `powerSum_cast` retains the same finite set when casting the natural sum into any semiring. This packet does not select a safe set, prove the controller reindex identity, choose a target residue, or assert a full native/polynomial witness. Those are separate integration steps. No positivity of a set's members is needed here; the two stated safety inequalities are the exact requirements. At `N=1` they force the support to be empty.

## Focused checks and development

The checks cover repeated-insertion idempotence, singleton increments, the complete sum cast into `ZMod`, unsafe last-cell rejection, the `N=1` empty-support consequence, source equality without marker bounds, and an actual two-position construction at `N=3`, stride `1`, for arbitrary tile assignment and Boolean markers. They construct both normalizations, without assuming any `F` increment or mask fact. Two independently supplied normalizations also give the same `F` for empty support at `N=1` and arbitrary displacement.

The first invocation was accidentally issued below the repository Lake root and rejected the unknown import prefix; it performed no proof compilation. The first correctly rooted main invocation passed unchanged. The initial checks exposed ordinary annotation/simplifier errors and reached the unchanged 6 GB cap during a closed `N=1` proof conversion. Corrected annotations and an opaque generic empty-support helper removed that closed conversion; the final checks passed at about 3.27 GB. No statement in the main module was weakened, no cap was raised, and no unsafe evaluation or additional axiom was introduced.

## Frozen bindings

All paths below are relative to the repository root.

| Artifact | SHA-256 |
|---|---|
| `Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentFiniteDummyMutation2011.lean` (181 lines, 9,246 bytes) | `7828e384536178637eedc37358f46edfc0979b32d2ec2634619815dd2e218601` |
| `Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentFiniteDummyMutation2011Checks.lean` (116 lines, 5,623 bytes) | `590d64607c38cd52b827986125c3d6642554a1f6894e56030d48b796912e4287` |
| Main `.olean` | `aaadd6758e09db0d2b1da19bcd300a20d7123e46e6e2b92c6c2e4615bbb9238f` |
| Checks `.olean` | `d965fe32c592d3ff263bbd8004f83c4bb682fcaf85856612c5d201a67f4e7958` |
| Direct `CurrentDummySafety2011.lean` dependency | `31f92f372076071c75ece964cb418c118fa051694057556c004d74a7353e7c00` |
| Imported `CurrentDummySafety2011.olean` | `987d72a91d4496ebe5273b9be53576455f04ba7340fb18c12991520ab5f3fcd6` |
| `lean-toolchain` (`leanprover/lean4:v4.32.0`) | `2773c517aa90b66ea8a2c52bddddf84393157797f8341be0df45294fff7fd32e` |

From the repository root, each new file was compiled serially using `lake env lean -M6000 -j1`, with `Elab.async false`, writing its own `.olean` under `.lake/build/lib/lean/DiophantineConsistency/`. The existing prerequisite objects were reused; this is not a fresh compilation of their transitive closure.

| Successful final run | Wall seconds | Peak RSS KiB | Exit |
|---|---:|---:|---:|
| Main | 3.86 | 3,294,936 | 0 |
| Checks | 3.72 | 3,265,224 | 0 |

Main diagnostics were empty apart from `/usr/bin/time` output. Checks emitted exactly thirteen requested axiom reports, all contained in `propext`, `Classical.choice`, and `Quot.sound`, with no warnings or errors. Source search found no `sorry`, `admit`, `native_decide`, `unsafe`, or declared axiom.

The final logs are `/tmp/current-finite-dummy-mutation2011-main.log` (SHA-256 `8072ceaf31f99bbb1a01ccfcb6292c0fb711dbc85c3c1f19fd6e44491c21ee0a`) and `/tmp/current-finite-dummy-mutation2011-checks.log` (`2bfae5b3e8dc92e87f41dbfb845b331cfde0684dc78dae12043a90dc4bdde186`). The `/tmp` paths are local run evidence, not durable repository dependencies.
