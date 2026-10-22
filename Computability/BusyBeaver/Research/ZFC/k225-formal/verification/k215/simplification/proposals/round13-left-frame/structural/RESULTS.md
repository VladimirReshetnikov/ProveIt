# Round 13: share the stack, totalize the one-step proof

Pin: `6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95` in
`VladimirReshetnikov/ProveIt`. Both patches are proposed source changes, not
compiled results. No repository write, push, or received script execution occurred.

## Lean: common stack semantics, not a generic enumerator

`EnumDom` and `EnumPerm` differ in command grammar, numeric packing, AX parameter
loading, and compiler blocks. Those differences should remain explicit. Their
underlying dominated AX stack, gated bundle, stream invariant, and elementary
stack proofs are already identical. Extract those into `EnumStack.lean` and
re-export their original source-level names from both clients.

The extraction contains 15 declarations: 13 declaration bodies are byte-identical
after removing doc comments; `good_zero` and `axStack_good` use the already shorter
current EnumPerm proof bodies. The five computational/logical definitions are
unchanged. The remaining client source is byte-for-byte unchanged except the
new import and export commands. This leaves each client's `St`, `W`, `Cmd`,
`cstep`, `execAt`, `run`, scheduler, block compiler and halting statement alone.

Full production-source counts, including the new module and adapter overhead:

- EnumDom: 711 -> 655 lines.
- EnumPerm: 545 -> 492 lines.
- New EnumStack: 70 lines.
- Total: 1,256 -> 1,217 lines, net 39 lines and 1,361 bytes removed.

Lean's `export` introduces elaborator aliases, including qualified names such as
`EnumDom.axStack`, without an extra kernel declaration or proof wrapper. See the
[official namespace reference](https://lean-lang.org/doc/reference/latest/Namespaces-and-Sections/#exporting-names).
This is the mechanism intended to let source consumers keep qualifications,
not a compiled compatibility claim. `CompatibilityAudit.lean` exercises fully
qualified aliases, `unfold`/simp, cross-namespace stack facts, and imports both
L2Root and Seed consumers; it remains uncompiled. It is not binary
compatibility for stale `.olean` files: downstream modules must be rebuilt, and
metaprograms that inspect original declaration identities must be checked.

Do not extend this extraction to Enum222.axStack: its generalized row is
`wal a h`, whereas these dominated variants use `wal u h`. Blindly sharing that
definition would change semantics. The patch introduces no unnecessary state
type or generic AX-policy parameter to hide this distinction.

Generator hygiene: the recent commit retired `generate_enumdom.py`. A static
scan of all 45 top-level Python files in the complete 59-entry `k225-formal`
listing identifies no current canonical EnumPerm writer. The remaining
`generate_enum222.py` writes only Enum222; the Dom/Perm references in L2
generators write the L2/seed clients rather than these enumerators. This is a
bounded top-level producer check, not a recursive proof that no script anywhere
can overwrite a file. The independent review records it in
`research215_round13_review/GENERATOR_HYGIENE.json`. Future generator changes
must preserve the shared module instead of restoring duplicate declarations.

## Rocq: one total outcome theorem, existing public API

The maintained `L1_SoundPerm.v` unfolds and cases on the numeric opcode separately
in `Inv_step` and `halt_step`. Prove one statement instead:

    step_sound s : Inv s ->
      match enum_step s with
      | Some s' => Inv s'
      | None => thm222 1
      end.

It has the existing four-command proof. The NIP case either obtains falsity from
the invariant's cached formula or pops a good stack. The other commands preserve
the invariant as before. `Inv_step` and `halt_step` retain their exact public
statements as one-line specializations; `Inv_run` and `enum_sound` remain textually
unchanged. This removes one duplicated opcode analysis, with no new interpreter,
global abstraction, invariant weakening, or halting convention.

The same patch replaces the custom `popn_S` induction with:

    Proof. unfold popn. apply Nat.iter_succ_r. Qed.

This reuses the exact existing theorem in
[Coq 8.18 PeanoNat](https://rocq-prover.org/doc/V8.18.0/stdlib/Coq.Arith.PeanoNat.html#Nat.iter_succ_r),
already available through the module's Arith import. Neither `popn` nor
`goodstack` is redefined. The one-step refactor saves four lines after wrappers;
standard-library reuse saves five more. Generated L1_SoundPerm: 98 -> 89 lines,
4,005 -> 3,648 bytes. Its hand-maintained producer under `rocqperm/` is also
patched (97 -> 88 lines, 3,862 -> 3,505 bytes), and the generated source hash
header is updated. Thus this is one nine-line proof simplification, or 18
lines/714 bytes across the two synchronized source-tree copies, not two
independent conceptual savings. This is deliberately a small improvement.

`regenerate215.py.calculus_files` reads the hand-maintained producer, changes
`From NS Require` to `From K215F Require`, and prefixes its SHA256. The owned
audit verifies that exact relationship both before and after the patch without
executing the received generator. A production regeneration should then
refresh `regeneration215.json` and rebuild the normal Rocq closure. The
standard-library citation above is explicitly Coq 8.18; neither that compiler
nor the maintained Rocq 9.1 environment was run here.

## What is and is not new

These patches do not claim the already implemented arbitrary-boundary EnumDom
halting theorem as new. They do not repeat the candidate-scheduling proposal,
the prior semantic Bisim/checker-adapter plan, the round-12 entry dispatcher,
the external KDenseBridge invariant refactor, or the PowerSets import cut.
Rocq's total one-step invariant uses the same useful outcome shape already
present in Lean EnumPerm, now concretely proposed for its maintained Rocq
counterpart. The novelty is this pinned, bounded integration, not the logical
idea of case-complete invariant preservation.

## Alternatives not selected

- Porting EnumPerm's decode/cstep/Option.map implementation into EnumDom would
  shorten some opcode proofs, but it also changes what L2RootDom.root_step must
  unfold. The shared-stack patch avoids that unnecessary scope expansion.
- A fresh shared candidate scheduler would repeat the already placed external
  candidate-scheduling packet. That is adoption work, not a new discovery.
- Replacing Rocq popn with a differently oriented Fixpoint is unnecessary:
  the existing standard-library theorem gives the saving without a definition
  change or a separate equivalence proof.

## Audit and adoption gate

Run `python build_proposals.py` from this directory. This owned script reads only
the bundled source snapshots, validates their exact Git blob identities, checks
the declaration extraction and retained text, regenerates both patches and all
proposed sources, and writes `AUDIT.json`. It executes no received proof code,
generator, or shell script. Unique proof maintenance totals 48 fewer lines;
including Rocq's synchronized generated copy the tree delta is 57 fewer lines
and 2,075 fewer bytes. Audit/compatibility-client files are not production
savings. Environment discovery is written separately to `ENVIRONMENT.json`,
so `AUDIT.json` remains portable. The
source audit is NOT a Lean/Rocq proof checker.

`REPLAY_CHECK.json` records that both patches pass `git apply --check` against
the pinned source snapshots and that replay reproduces all canonical outputs
byte-for-byte. It excludes the machine-dependent environment file. Python
optimization is rejected explicitly because the source checks use assertions.

All four of `lean`, `lake`, `rocq`, and `coqc` are absent from PATH here. Before
adoption, compile EnumStack and both enumerators, then their L2/seed consumers
and the K215 endpoint. The K217 full endpoint has separately reported stale
machine-specific inputs at this pin; do not call that full endpoint checked
merely because EnumDom/SeedDom build. For Rocq, rebuild L1_SoundPerm, SeedPerm,
and the maintained endpoint and run recursive `coqchk`/the established axiom
audit. Keep every existing public statement and verify unchanged endpoint
assumptions. No speed or memory improvement is measured or claimed.

`PROVENANCE.json` contains pinned URLs and exact Git blob SHAs. `SHARED_STACK.patch`
and `ROCQ_STEP_SOUND.patch` are independent and can be reviewed separately.
