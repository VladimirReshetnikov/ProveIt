# Pinned source subset

The two Python files in this directory are unchanged copies. The manifest
records their source paths, commits, byte counts, and SHA-256 digests.

1. `theory_backend_experiment.py` is from the ProveIt research tree, commit
   `ce89d875857e59e147becd7f34a7c5ea8d18180b`:
   <https://github.com/VladimirReshetnikov/ProveIt/blob/ce89d875857e59e147becd7f34a7c5ea8d18180b/Computability/BusyBeaver/Research/ZFC/theory_backend_experiment.py>.
   The retained `LICENSE.ProveIt` applies to ProveIt-authored material.

2. `upstream/ZF/m254/tools/logic/spec.py` is from Jeff Ketchersid's
   `jeff87654/busy-beaver` tree, commit
   `297ab8df7e5de329605c3875b4934643b371a5e3`, via ProveIt's pinned snapshot:
   <https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/tools/logic/spec.py>.
   Mira-Cult designed the original compact calculus and machine; Jeff
   Ketchersid supplied the symbolic specification and formal verification.

ProveIt's import notice states that no upstream-wide license is declared
in the pinned busy-beaver tree and that the imported snapshot is excluded
from ProveIt's blanket MIT-0 grant. This small source subset preserves that
boundary and does not relicense the upstream specification. Full upstream
import provenance is at:
<https://github.com/VladimirReshetnikov/ProveIt/blob/ce89d875857e59e147becd7f34a7c5ea8d18180b/lib/jeff-busy-beaver-zfc254/README.proveit.md>.

The emitter checker executes only the pure definitions described in the
packet README. Unrelated experimental theory modifications present in the
complete unchanged research source are not executed or endorsed here.
