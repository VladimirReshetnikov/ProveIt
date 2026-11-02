# Unlaunched coherent difference-ring rebuild plan

The newer `ModelDifferenceRing` source defines `DiffRing V` as a commutative
ring and supplies `split_evalRing` and `internalZero_iff`. A future proof can
instantiate the already proved universal denominator-cleared identity in that
ring and then bind its four parameters to the 95-row graph. That could avoid
expanding eight signed coordinates. It would prove an algebraic transport
only; denominator divisibility, integrality, strong norm and the compact44
checker remain separate obligations.

The source-only freeze ran `fresh-project-closure/prepare.py` for
`DiophantineConsistency.ModelDifferenceRing`: actual process exit 0,
19 declared project modules, 17 direct external modules, manifest SHA-256
`859169fa08540764d0b02864fdeb7906301afcf4e1fea1e4b0e689c90df491b4`.
The frozen Git HEAD is `09bdb5b03a3f39c8795b8292e6f0a87296373efd`. The copied
manifest pins all 19 source hashes, imports, Lean config hashes and names;
its paths reference the temporary freeze, so reconstruct from that pinned
Git tree rather than assuming the temporary files persist.

The `audit_plan.py` comparison exited 0 after one initial path-root error; it
checks that all 64 distinct files in the union of the 19-source graph and the
historical 62-source rank closure equal the pinned tracked Git blobs. The
union contains two files absent from the historical snapshot:
`ModelDifferenceRing` and `WeightedExpressionDegree`. `NaturalExpression`
changed; its import names did not. The historical source-declared reverse
closure of that change includes **27 of the 62** rank modules, printed by the
checker. All other historical source bytes in this union match. This is a
source/header survey, not Lean's authoritative dependency parse or a build.

Other newly received modules—`DiscreteOrderedRingFacts`, `ModelArithmetic`,
`ModelCarrierScaled`, `ModelCarrierCurrent`, `ModelCarrierSpheres`,
`ModelCarrierChecks`, and `ArithmeticPellPigeonhole`—are not in this
19-module closure and are not needed for the basic ring-homomorphism plan.
Their addition to a later target requires a fresh closure and fresh rebuild;
no compatibility of their objects with the historical provider is assumed.

At the recorded measurement `/tmp` had 6,095,970,304 bytes available. The
62 historical parent artifacts occupied 42,965,976 bytes; the 27 affected
artifacts occupied 19,274,200 bytes. Seven previously generated fresh FreeJ
objects occupied 5,465,032 bytes. The new `ModelDifferenceRing` and
`WeightedExpressionDegree` sources occupied 12,271 and 2,698 bytes; the
changed `NaturalExpression` source occupied 4,024 bytes. Source length does
not bound compiled artifact size. These are point-in-time measurements, not
predictions of memory, temporary space, runtime, or successful compilation.

A separately reviewed implementation should:

1. Freeze the complete source-current union, its config, exact compiler and
   package/Foundation inputs; include the exact research source closure for
   the FreeJ graph, factor split, ordinary-tail identities and new bridge.
   Recompute actual compiler direct dependencies, and reject missing,
   shadowed, changed or untracked source and namespace fallback artifacts.
2. Use two separate empty project output trees and compile **all** selected
   project modules and bridge sources anew in topological order against the
   same independently authenticated Foundation/package provider. Do not use
   old project objects, including the apparently unchanged 35 objects or any
   generated FreeJ object; compare the complete sibling records and outputs.
3. Start only after independently reviewing the driver and exact snapshot.
   A proposed **512 MiB per sibling** is a planning budget, not a cap that the
   current scripts enforce. Sample free space before, during and after each
   run and stop when a sample falls below **4 GiB**; sampling cannot guarantee
   that the threshold is maintained between samples or against other users.
   Also stop on any dependency, source, companion or terminal-exit failure.
   Two 512 MiB budgets would total 1 GiB, but compiler temporary files,
   concurrent writers and new output sizes remain unknown. No launch is
   authorized by this planning receipt.
4. Preserve actual outer and compiler exits, direct dependency resolutions,
   source/object/companion hashes, axiom reports and all failures. An
   independently reviewed artifact audit is required before treating either
   replay as evidence. Package-transitive and dynamic loads need explicit
   coverage or must remain stated limitations.

The plan does not assert a compiled difference-ring bridge, a model proof of
integrality, or an internal iPRA proof. The 64-source count is a conservative
union from existing source-declared graphs; any new bridge or changed import
can enlarge it, and current source drift must be rechecked immediately before
freezing. No build was launched in this survey.

## Storage-control assessment

At the later probe, `/tmp` was on `/dev/sda2` (`ext4`, mount options
`rw,relatime`), with 6,094,270,464 bytes available. The current user was UID
1000; `setquota` was unavailable and no project quota was reported in the
mount options. `prlimit` is available, but its file-size limit is per file,
not an aggregate project-tree quota. A non-destructive user-namespace probe
successfully mounted and unmounted a 1 MiB tmpfs in a private namespace.
`bwrap` is present. A bounded tmpfs combined with a separately reviewed
read-only filesystem sandbox and writable scratch, including compiler temp
paths and logs, is a possible aggregate scratch limit; the probe did not test
that setup. Tmpfs may use swap, and other processes may consume disk, so it
does not by itself guarantee 4 GiB of host free space. A filesystem/project
quota or reserved filesystem covering all writes could enforce a scoped cap
if available; none has been established here. A reserved allocation might
protect reclaimable capacity but is not the same as keeping `df` free space
above the threshold. No quota, scratch mount, reservation or build is left
active by the probe.
