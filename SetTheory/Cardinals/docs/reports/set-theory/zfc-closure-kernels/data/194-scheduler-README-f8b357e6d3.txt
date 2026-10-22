Combined patch and producer integration check
============================================

The four numbered patches are ordered as follows:

  01_shared_implication_lean.patch
  02_scheduler_lean.patch
  03_scheduler_rocq.patch
  04_shared_implication_rocq.patch

Baseline: VladimirReshetnikov/ProveIt commit
57541fe0cfe3af62b4cb58747d8d1d7c16b338d5.

Reproduce with Python 3.10+ and Git:

  python3 check_patches.py --repo /path/to/ProveIt \
      --patches /path/to/patches --out /tmp/k215-patch-evidence

Keep check_patches.py, integration_manifest.json and check_rocq_producer.py
together. --out must name a new directory outside the ProveIt checkout.
No proof assistant, network access, or complete endpoint build is required.

The checker reads HEAD and validates all baseline and patch hashes. It copies
only 38 existing files into an isolated temporary directory: affected source
paths and unchanged producer prerequisites. Seven expected-new paths are
checked absent. It then runs git apply --check followed by git apply for each
patch, in order, exclusively in that temporary directory. Every intermediate
and final patch output is hash-checked. The original checkout is never patched;
its relevant source hashes are checked again at the end.

The applied files cover 23 distinct repository paths. Thirteen proof-source
hashes are matched with the delivered checked components: eight Lean sources
(the seven modified/new production proofs plus unchanged DomRho8) and five
Rocq sources. The latter match the original source hashes in the Rocq build
receipt; that build separately records the Stdlib/Coq namespace compatibility
substitution where required by the available compiler.

Producer checks use only the temporary applied tree:

* The maintained Lean shared-basis wrapper reproduces/checks all three Lean
  outputs using the restored six-goal plan and the pinned templates.
* The unchanged Enum222 and EnumDom fork generators reproduce both refactored
  clients from the applied Enum254 source, byte-for-byte.
* The supplied Rocq producer checker invokes the actual patched
  regenerate215.calculus_files function. It compares DominatedImplication,
  DomRho8, CandidateScheduler, L1_CompPerm, and SeedPerm byte-for-byte.
  Its unchanged imported Python modules and 217 calculus templates are copied
  and pinned as part of the minimal input set.

This validates patch ordering, source correspondence, and the affected
producer paths. It does not repeat the Lean/Rocq proof checks, regenerate the
physical machine, or rebuild the full machine/ZFC endpoint. Separate component
receipts supply proof-compilation evidence. Temporary-directory prefixes in
the captured logs and Rocq producer receipt are normalized for portability.

The evidence directory contains the completed integration receipt, command
logs, and the Rocq producer's five-output comparison receipt. No staged source
copy or compiled object files are needed in the final archive.
