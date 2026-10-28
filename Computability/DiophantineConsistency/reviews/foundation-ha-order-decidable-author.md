# HA decidability and stability of the interpreted strict-order atom

Author: the `circuit_reduction` agent. This is an author receipt, not an
independent review. The agent authored this pair and the replay driver, and
previously authored the reused trichotomy, irreflexivity, transitivity and
several HA syntax/arithmetic leaves. Root performs independent acceptance.

## Exact proof scope

`FoundationHAOrderDecidable.lt_decidable s t` proves the object-language
formula `ltFormula s t ∨ ¬ ltFormula s t` in the existing conventional
`HA.Proves` calculus for arbitrary PAHF terms, including arbitrary free
parameters. This is neither a Lean `Decidable` instance for standard-natural
semantics nor merely a GG-translated decision formula.

The proof uses the existing plain HA trichotomy theorem. Its positive branch
introduces the left disjunct. Equality refutes strict order by equality
transport and irreflexivity. Reverse strict order refutes it by transitivity
and irreflexivity. Both refutations are proved with explicit finite open
contexts. The transport hole is slot zero, and the entire left parameter is
renamed by successor before equality elimination; instantiating that hole
therefore preserves all original free variables, even occurrences of slot
zero in a compound parameter.

`lt_stable s t` then proves `¬¬ltFormula s t → ltFormula s t` using ordinary
intuitionistic case analysis on the proved decision formula. `recover` applies
that theorem under an arbitrary finite context. No new general DNE or
excluded-middle rule, model-semantics premise, classical PA proof oracle, or
arithmetic-image axiom is used. This new pair introduces no additional formula
induction; it reuses the actual formula-induction proof of trichotomy.

The focused checks bind the actual Foundation positive order atom's GG image
to `doubleNeg (ltFormula (var 0) (var 7))` by `rfl`, and recover the ordinary
order formula from that literal image. They also cover equal terms, zero and
successor zero, sparse nested multiplication/addition parameters, equality
transport under two explicit assumptions, successor-renamed contexts, and
two universal closures retaining a free parameter at slot seven.

## Frozen files and fresh validation

Both files are under `Lean/DiophantineConsistency/`.

| File | Lines | SHA-256 |
|---|---:|---|
| `FoundationHAOrderDecidable.lean` | 80 | `353549b5ac2dcc51e84b7a8ac7f9714cd66e7eaa28e1df90007ed7598b3ba006` |
| `FoundationHAOrderDecidableChecks.lean` | 57 | `19a331e01a1b4b409f8abd077b452fa0c060b2b5ffe7325bbfb5a68fdfb291bf` |

The complete new sources and all 211 lines of the driver were read before
execution. Both fresh invocations passed on their first attempt; there were
no failed Lean drafts or intervening source edits. A later read-only lookup
used a nonexistent checks pathname, then was corrected; that did not execute
or mutate any Lean source.

The private output directory is
`/tmp/ha-order-decidable-author-suitwa7p/lib`. Each invocation used Lean 4.32.0,
the full actual source pathname, `-M6000 -j1 -DElab.async=false`, and a 512 MiB
free-space reserve. Only the two new private `.olean` files were written; no
dependency object, symlink output, accepted source or vendor file was changed.

| Fresh object | Seconds | SHA-256 |
|---|---:|---|
| Main | 1.70 | `d808204fd0e3efc97ef90e9cbfd16189ca2d8aca72984a96fadfafacc01efa9c` |
| Checks | 1.69 | `7b73c3090899f4b4b532954fbe8a1b708a5683c66806a690d5ed40770a56ff8e` |

The main log is empty. All twelve axiom reports contain only `propext` and
`Quot.sound` (the literal GG binding uses only `propext`). No report contains
`Classical.choice`, `sorryAx`, or a new axiom. These reports describe Lean
metatheory dependencies; the object-language statements are actual HA
derivability assertions with the existing intuitionistic rules.

## Reused closure and durable records

The driver selects exactly **98 cached current-source modules**, including
**76 Foundation modules**, from the authenticated closed HA ZFC/validator
inventory. There are **326 cached artifact files**, **34 explicit external
boundary import names**, and **602 deduplicated pre/post pins**. It checks the
accepted parent records, compiler/toolchain/manifest, every selected source,
every selected import header, and recorded objects/companions. It rejects a
reused client importing either fresh leaf or any unresolved custom import.
The selected package boundaries remain explicitly reused boundaries; this is
not a fresh replay of Foundation, Mathlib, or the full earlier HA closure.

All pins match before and after each fresh invocation. The exact sources,
commands, logs, compiler outputs, parent snapshots, input inventory and result
are preserved in the 12-file `foundation-ha-order-decidable-replay/` bundle.

* Summary `foundation-ha-order-decidable-replay.json`:
  `8faf1939ce456aa1581cdb68c5f0a004e54af412a10830a693dd12f8799e23f9`.
* Bundle `FILES.json`:
  `8f24d08ce7544f4ba4c625f7271ea3992fb890ed3266fab6d54c214989d2ebb4`.
* Terminal `attempt-1793062440676962386/RESULT.json`:
  `cdabc815ffedb924d6e9841afc47b6e1a35ff67151fbc388b7798d9e6e7bed23`.
* Input inventory:
  `0ff2467c84b7b0b3b27473a46c1928fd1fa418b9f57f27e4d699d672ade2cb4e`.
* Driver:
  `8696ea5938b0d44a2dbb427cecef1766bf7bfb2648137d24dbe105ea3e06a708`.

## Remaining boundary

This is a genuine HA order-atom decision and stability checkpoint. It does
not prove decidability or GG equivalence for arbitrary bounded matrices,
normalize the actual proof-checker predicate inside HA, identify the fixed
GG consistency target with an untranslated checker, or prove the current
equation's desired HA equivalence. No maintained equation artifact changed.
