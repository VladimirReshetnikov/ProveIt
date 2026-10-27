# Literal permuted C222 one-command graph — author receipt

Status: **PASS**, 2026-10-26. This packet represents the actual `EnumPerm.cstep`
working-register effect over arbitrary internal IOpen inputs. It is not a run,
scheduler, semantic seed, consistency, or HA-equivalence theorem.

## Frozen source and fresh results

| File | Lines | SHA256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/ArithmeticCommandStepPerm222.lean` | 280 | `98f3c3fea0f1cb3a5f6d5f1e46e7cc33a1181a8545aeff114dc86dd28062e4dc` |
| `Lean/DiophantineConsistency/ArithmeticCommandStepPerm222Checks.lean` | 61 | `770cdac6f175fa70ebaee33125ee61aa259d505d7e79f56ce59e4a45e36bde99` |

The final source, checks, and replay driver were read in full before execution;
the complete source and the subsequent small correction were reviewed against
the actual `EnumPerm` definitions and accepted constructor graphs. The two fresh
compiles passed in 22.12s and 2.06s. The main log is empty.
All twelve axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound` (the raw repacking theorem uses only the first and third). No
`sorry`, `native_decide`, or new axiom occurs. Reported child-process maximum RSS
was 1849800 KiB across the sequential run.

Fresh objects:

- Main: `1b79af9c353f9a386a9edd49f30be52ea9b9686615dc537d7cb858b6243496fe`.
- Checks: `3b60ec3b03100a0e7fffaa9227c23780ba9b655d233837c19845ec59336c1e63`.

## Exact arithmetic binding

`stateValue t s d h = P(t,P(s,P(d,h)))`; success is that code plus one, while
zero denotes a halting NIP. `effectValue k p q t s d h` interprets the literal
opcode and first/second payload fields: opcode 0 is NIP and opcode 1 is DROP,
both preserving `d`; opcode 2 is MP with increment `p`; otherwise AX reads
`p=y,q=x`, sets `a=d+x,b=h+y,c=k−3`, and supplies the old `d` as `u`.
The exported dominance fact is derived `d≤d+x`, not an extra supplied premise.
MP tests exactly `wim t (d+x)=h`, without a validator successor or predecessor
condition. A failed MP may return the successful allzero state, coded one.

The ten AX stack entries, head first, are precisely
`rho1(a,b),rho2(a,b,c),rho3(a,b,c),rho4(a,b,c),rho5(a,b,c),rho6(a,c),growG(a,b,c),rho8(a,b,c,u),wal(u,h),t`,
followed by the old stack. Fresh-label collisions yield truth code zero as the
top field; they do not halt AX. The gate uses the actual helper-free C222 bundle.
The represented graphs retain unbounded intermediate witnesses, so neither a
shrinking output nor halt zero imposes an unjustified intermediate bound.

`stepValue_eq_zero_iff` states exactly opcode zero and cached code one.
`stepValue_pack_nat` binds all actual command constructors and arbitrary rest
pointers. `pack_decode` reconstructs every raw natural code, and `stepValue_nat`
therefore proves exact `EnumPerm.cstep (EnumPerm.decode raw).1` agreement for
**every** raw code and every working register tuple, without validity or typing
premises. The new leaf imports no old `ArithmeticCommandStep254` effect.

Checks include literal short-command counter preservation, AX argument and
GEN orientation, both numeric freshness collisions, raw cached-falsity NIP,
failed-MP successful-zero state, and universal raw/packed-command adapters.

## Dependency and execution provenance

The private overlay is `/tmp/stepperm222-author-9m_di_mj/lib`. It reuses exactly 106 current-source
custom modules, including 86 Foundation modules, with 364 existing companion
artifacts. There are 37 explicit external import names, including Init. The
closure is the independently replayed parser closure plus the parser leaf and
four accepted source-identical constructor leaves: `ArithmeticCode254`,
`ArithmeticTemplates254`, `ArithmeticTemplates222`, and
`ArithmeticSeedTemplates222`. All four added source/object pairs were checked
against the accepted SeedClosure222 inventory; recursive import order and every
selected source were checked afresh. All 646 pinned files matched before and
after execution. This is authenticated reuse, not a fresh Foundation rebuild.

Compiler: Lean 4.32.0, SHA256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Each invocation used `-M6000 -j1
-DElab.async=false`, with an explicit private LEAN_PATH and a 512 MiB disk-reserve
guard. Dependency symlinks were read only. Each attempt used a new private
overlay with absent, nonsymlink output destinations; no shared object was
modified. The fixed-Nat consistency pair was not compiled by this driver.

The durable summary is `reviews/arithmetic-command-stepperm222-replay.json`
(SHA256 `b33083184d10070b7c7c197d5d7dd3e0eaedfde3eef87b8b7c2495f8a5aafbd3`), and the complete bundle is
`reviews/arithmetic-command-stepperm222-replay/`, with its own `FILES.json`.
Final RESULT SHA256: `ba06c6c16544a5808828187e6feda5ecb14f6a896a807c04dcdb13feab4f274d`. Final inputs SHA256:
`fd49610ca0d5c5620506d6c1b39928f624f2bc73b8f9aa679690140cf59b5b4a`.

## Preserved development failure

Attempt `1793060470771056652` failed after 22.08s: the three raw Cantor-repacking
steps attempted to use `Cantor.toNat_ofNat` without explicitly unfolding the
locally irreducible `Code254.P`; four redundant simp arguments also produced
warnings. The corrected proof explicitly unfolds only `Code254.P` and
`EnumPerm.unP` in those three steps and removes the unused arguments. No
statement, graph, or register effect changed. The failed source, diagnostics,
and run record remain separate in the bundle. The final attempt is
`1793060521836843964`.

Authorship: circuit_reduction authored this pair and previously independently
reviewed the root-authored parser. The primitive C222 constructor graphs are
reused from controller_certificate's accepted work. No new proof of internal
C222 validity, bounded-run preservation, scheduler completeness, or a machine/
consistency endpoint is claimed here.
