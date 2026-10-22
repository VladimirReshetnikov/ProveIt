K215 Lean compiler fusion: checked component proposal
===================================================

Baseline: ProveIt 6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95.
Toolchain: Lean 4.32.0, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35.

Idea
----
Interpret the existing dominated-implication theorem directly in the predicate

    Can(n) := exists p : List Cmd, EnumPerm.Contract p n.

The existing mp_contract proves closure under modus ponens. The existing leaf
compiler and cexec_discard_ax prove the restricted rho8 instances when u <= a.
DomRho8.rho8_all_of_restricted therefore proves that every unrestricted rho8
instance is compilable. An induction on C222 now builds command contracts
directly. The intermediate conversion from C222 to CDom and its subsequent
compilation are no longer on the active K215 proof path.

Contract deliberately permits an early halt as well as the required output.
Using the existing contract preserves that feature in the generic implication
interpretation; it does not assume every compiled block terminates normally.
The operational functions, physical machine, source certificate and logical
calibration remain unchanged by this proposal.

Files
-----
compiler_fusion.patch modifies EnumPerm and adds EnumPermCompat.
sources/ contains the proposed sources and two typed audit clients.
prepare_fusion.py reproduces the exact patch from the pinned checkout.
build_fusion.py performs the isolated fresh compilation and baseline comparison.
source_metrics.json counts the selected changed sources.
closure_metrics.json inventories all sources in the baseline/proposed static
  endpoint and enumerator import closures, with SHA-256 identities.
check3/receipt.json and check3/logs/ are the accepted build record.

Check scope
-----------
The accepted run freshly compiles 16 project modules and two typed audit
clients. This includes both the 14-module active enumerator closure and the
two extra modules needed by the legacy compiler interface. It then recompiles
the original EnumPerm and a baseline audit client, reusing only identical
dependency objects produced in the first part of this same run.

Every invocation in check3 returned zero. The new compiler, complete and
halts_iff print exactly [propext, Classical.choice, Quot.sound], as do the
corresponding baseline results and the compatibility build theorem. Six
preexisting warnings occur in unchanged TarskiComplete. The proposed modules,
baseline EnumPerm and all audit clients have no warnings.

The full machine-to-ZFC endpoint was NOT rebuilt. Its closure counts below
are static import measurements, not full-endpoint compilation results.

Initial unsuccessful attempts are retained separately: check1 failed when
Lean could not infer the predicate parameter of rho8_all_of_restricted; the
fixed call makes T explicit. check2 compiled every proposal module and client,
then failed only in the comparison runner's baseline object search path.
check3 corrects that runner by copying the identical compiled dependency tree
before recompiling the baseline module. Neither earlier attempt is called a
complete passing comparison.

Measurements
------------
Full static KEndpoint215 closure, excluding Lean's standard-library Init:

    project modules      178 -> 177
    UTF-8 source bytes   2,093,112 -> 2,091,052
    physical lines       40,517 -> 40,452

The removed active module is KCodeDom (2,617 bytes, 73 lines). EnumPerm grows
from 22,788 to 23,345 bytes and from 545 to 553 physical lines. Thus the active
proof closure saves 2,060 bytes and 65 lines, about 0.0984 percent of its bytes.

The new compatibility module adds 581 bytes and 16 lines off the active
endpoint path. KCodeDom is retained for other clients. This proposal does not
reduce total repository source storage: it simplifies the active dependency
path and removes an intermediate derivation representation. The archived
compatibility cost must not be subtracted from the active-closure figure or
silently omitted from a whole-repository comparison.

API migration
-------------
EnumPerm.build_c222 is the new direct compiler. The old EnumPerm.build type,
which accepts CDom, is preserved in EnumPermCompat. A legacy client using that
specific theorem must import BusyBeaver.ZFC.EnumPermCompat. Existing imports
of EnumPerm alone no longer expose build or the unrelated transitive CDom API.
The public complete and halts_iff statements are unchanged. The maintained
K215 endpoint imports only EnumPerm, through its ordinary program layers.

Before production adoption, rebuild the changed endpoint descendants and
repeat the endpoint axiom audits. Refresh KEndpoint215's explanatory comment
about the compiler passing through CDom; its theorem bodies need no change.
Do not replace KCodeDom globally: EnumDom and historical compatibility clients
still use it.

Reproduction
------------
Run from this directory, giving absolute paths to a checkout and Lean:

    python3 prepare_fusion.py /path/to/ProveIt
    git -C /path/to/ProveIt apply --check /path/to/this/compiler_fusion.patch
    python3 build_fusion.py --repo /path/to/ProveIt \
      --lean /path/to/lean-4.32.0-linux/bin/lean --out /fresh/output/path

The output path must not already exist. Project inputs are recompiled;
the standard library supplied by Lean is used normally. The scripts do not
modify the checkout or download anything. A source hash identifies bytes and
does not replace the kernel checks. Timings in the receipt are local component
observations and do not establish a full-endpoint speedup.
