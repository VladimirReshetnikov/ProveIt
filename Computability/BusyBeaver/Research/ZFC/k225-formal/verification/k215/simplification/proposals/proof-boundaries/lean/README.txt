K215 / K217 AX-word simplification
================================
Baseline: VladimirReshetnikov/ProveIt
Commit: 6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95
Lean compiler used: 4.32.0

This packet offers TWO ALTERNATIVES, not consecutive patches.
Apply local.patch OR shared.patch to the baseline, never both.
The repository itself has not been modified.

1. Recommended first change: local.patch
----------------------------------------
The AX word currently stores (macro, successor) pairs. The successor is already
available in the literal register program. Store only the macro sequence, and
let the checker read the successor from p.nodes n. The checker rejects any
non-node pair, mismatched macro, or finish at a node other than the terminal
gate 457. The same induction proves the arbitrary-register run contract.

The patch changes both generated AX modules and their generator, retaining
independent proofs for the two programs. Each file goes from 161 to 155 lines.
K215's file goes from 7,563 to 6,533 bytes (1,030 bytes, 13.62%). It introduces no
new module into K215's dependency closure. Each certificate still lists all
156 semantic macros; exactly 156 redundant successor numbers per file disappear.
The public machine-facing f236, l236, c236 and ax_eval interfaces are retained,
as verified by compiling the unchanged L2RootPerm, L2RootDom and SeedPerm.
The certificate-helper API changes from pairs to atoms.

Including the producer, the two-module local patch reduces 537 to 532 physical
lines and 23,903 to 21,926 bytes. This is mostly a certificate-data reduction;
it does not remove an induction or change the trusted computing base.

2. Larger maintenance change: shared.patch
-------------------------------------------
Move the AX macro effects, base contracts, gate proof, checker soundness,
cleanliness, literal semantic word and symbolic evaluation into AXWord.lean.
Keep thin literal bindings for each program, using their existing transfer
lemmas. The two semantic words differ ONLY by commuting readp1 and cons at
zero-based positions 6 and 7. They read fields in the same order.

readp1 updates p1 and pl. cons updates tw and ws. Thus their effects commute
for every nine-register record, definitionally: the commutation is proved by
rfl. Evaluations of the complete words are also definitionally equal. One
symbolic evaluation therefore serves both programs. Each literal program must
still pass its own kernel check; cross-applying the words is rejected.

Shared Lean sources: 322 -> 226 lines; 15,099 -> 9,754 bytes (35.40%).
Including the generator: 537 -> 296 lines; 23,903 -> 12,546 bytes.

The aggregate saving is not a reduction of the K215 endpoint's own imported
AX source. For K215 alone, AXWord + its wrapper total 195 lines / 8,511 bytes,
versus the old 161 lines / 7,563 bytes: +34 lines and +948 bytes. Choose this
alternative for maintaining both machines with one proof, not to minimize
K215's dependency closure. The shared core is maintained Lean source; the
shortened producer regenerates the adapters and validates the chain shape.
The literal checker remains the authority on the actual program's word.

3. Verification scope
---------------------
verify.py builds every project module in the target closure from source, in
serial, and records source SHA-256, imported project source fingerprints,
produced olean SHA-256, compiler identity, baseline commit and exit status.
No cached project objects are reused. The standard library comes from the
recorded compiler distribution. A global lock avoids overlapping proof builds.

Both alternatives compile both unchanged root-step clients and the K215 seeded
program theorem. AXAudit also checks rejection of a wrong start node, a wrong
macro and a truncated word. The shared variant additionally rejects each
program paired with the other program's word, despite equal effects.

Final retained evidence lives in evidence/local and evidence/shared. The
local closure has 35 modules; the shared closure has 36. Axiom reports for
l236, ax_eval, root_step and dagPerm_seed_iff are exactly the standard trio
propext, Classical.choice, Quot.sound. The two shared commutation/evaluation
identities use no axioms. There is no sorry, unsafe declaration or native_decide.

These are targeted refactor checks. The full binary-machine endpoints,
certificate modules, complete release build and Lean kernel re-auditor were
not rerun. No whole-endpoint speedup is claimed. Before merging, run the
repository's full serial endpoint gate at the chosen final source revision.

Run (from this packet directory):
  python3 verify.py --repo /path/to/ProveIt --lean /path/to/lean --variant local
  python3 verify.py --repo /path/to/ProveIt --lean /path/to/lean --variant shared

Check patch applicability (from the repository):
  git apply --check /path/to/local.patch
  git apply --check /path/to/shared.patch

The two generate_l2axiomsdom.py copies have the existing CLI:
  python3 generate_l2axiomsdom.py NODES_JSON OUT_LEAN [perm]
Use lean215/dagperm_nodes.json with perm and lean217/dagdom_nodes.json with dom.
Both generators were checked to reproduce their corresponding two submitted
Lean files byte-for-byte. The exact counts and hashes are in evidence/metrics.json.

4. Secondary current-source observation
--------------------------------------
The new SeedDom imports Seed222 only to obtain L2K.bootRegs. This unnecessarily
imports L2Root222 and L2Axioms222 into the K217 lane. Extracting bootRegs into a
data-only module would remove that import chain. This observation does not
apply to K215: SeedPerm already imports only L2RootPerm. No such import patch is
included, since it is outside this packet's verified scope.
