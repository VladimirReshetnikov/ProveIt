# Verification evidence

The primary route is `python3 -B portable/reproduce.py --output-dir EMPTY_DIR`.
It reconstructs the exact sources/tables and freshly rederives all three
unbounded runtime proofs. See the packet README for mode distinctions.

The source and case receipts under `certificates/` are successful mathematical
checks of the exact distributed input hashes. Runtime summaries record the
unmodified engine/helper hashes, all ordered generic cases, full transition
coverage and independently checked list-block lemmas. `runtime_origins.json`
records the independent derivations used for the stored certificates. The
portable audit rewrites their integrity receipt against the actual distributed
checker. Re-running a symbolic proof can change elapsed seconds but not the
literal inputs or per-case mathematical results.

Supplementary independent checks:

- `independent_small_audit.py` parses literal tables and source without
  importing packet code, repeats full sparse/dense startups and checks the
  source guard, exact reassociations and distinct composed physical seed.
- `independent_source_check.py` reconstructs both complete tree-transform
  orders and checks all-natural control transport and exact table patches.
  `source_transport.json` and `PROOF_SOURCE.md` are its accepted results.
- `independent_runtime_audit.py` checks the delivered runtime/case bytes and
  derives the four block identities without importing the runtime engine.
  Its result is `independent_runtime_receipts.json`.
- `archive_chain_audit.py` recursively checks CRCs, safe regular archive
  members and every available exact manifest in the seven inherited ZIPs.
  Its result is `inherited_archive_chain.json`.
- `negative_controls.py` rejects ten malformed source/case/block/startup
  inputs. `manifest_boundary_tests.py` rejects four private-copy corruptions
  of inventory, file bytes, path safety and checksum index. These controls
  test the checker boundary, not the machine's unbounded behavior.

The optional checkers have explicit CLI path options (`--help`). Their saved
receipts contain input hashes and can be compared with the shipped files.
The independent source checker keeps its original research-layout defaults;
the main driver supplies every path explicitly and uses no outside file.

`quick_replay/` records a successful pre-seal full-chain quick-mode test with
logs. Its inventory count predates addition of release reports and final audit
receipts; this is not a claim that the snapshot was the final ZIP. The default
isolated replay and final inventory/binding receipts identify the final code
and machine payload separately. A final seal does not rerun a symbolic proof
merely because an explanatory PDF or audit receipt was subsequently added.

`baseline_full_replay.json`, `baseline_full_runtime_audit.json`,
`baseline_intake.json` and `baseline_independent_intake.json` are historical
successful evidence for the exact unchanged upstream K219 packet. They are not
alternative-machine runtime certificates. Current logical inheritance is
replayed through the operative vendor manifests and recursive construction /
calibration scripts. Development receipts inside the unchanged vendor ZIP are
not relabeled as fresh current-byte proof endpoints.

None of these files proves consistency, unconditional nonhalting, minimality,
or a 218-state construction. The ordinary mathematical certificate boundary,
including the absence of a new exact-byte proof-assistant endpoint, is stated
in the main README, NOTICE and report.
