# Carrier65 retry05 prefix: bounded continuation feasibility

The preserved 239-stage prefix has enough *observed recorded material* to
justify investigating a separate continuation, but this inspection does **not**
show it can safely be reused or provide a launch-ready runner. It makes no Lean
call, creates no output in the preserved tree, and makes no change to prior
state. The [resumption audit](../current14-carrier65-retry05-resumption-audit/README.md)
established that the original fixed-output runner cannot resume; it must not be
rerun against or used to overwrite the preserved failed attempt.

An [independent review](../../reviews/current14-carrier65-retry05-prefix-feasibility-independent/README.md)
rechecks the recorded prefix, routes, guards and pending slots. It does not
establish provider compatibility or make a continuation build-ready.

## What survives and agrees now

The receipt pins the plan, failed state, outer record and base state, and
checks the following at one non-atomic point in time:

* All **529** planned source files and their copies in the retained source tree
  match their planned source hashes. The separate final audit client's source
  and its snapshot also match. This byte comparison is not a current Git
  cleanliness or full transitive-source certificate.
* All **239** completed `.olean` outputs match their recorded hashes. For each
  output the original runner recorded 13 possible output suffix paths: 239
  `.olean` files are present and all **2,868** other recorded output slots
  are absent. Absence does not prove that no implicit companion, runtime or
  package file is required by a future Lean invocation.
* All **478** archived and retained live child logs match the stored hashes
  and successful recorded monitor results. All **1,000** recorded base
  `.olean` links still resolve to the recorded files and hashes. This does not
  authenticate the entire transitive history behind those base artifacts.
* The 239 rows record **716** direct dependency edges: 325 to earlier prefix
  outputs, 48 to base producers, and 343 to explicitly listed external
  objects, including `Init`. Their recorded paths, current hashes, resolved
  producer paths and observed first `.olean` candidates match the plan/base
  evidence. The **12,090** distinct captured direct-guard paths still agree
  with their recorded presence, realpath and hash or recorded absence. This
  checks retained records and current files, not a new `lean --deps` run or
  a complete package/toolchain/dynamic dependency closure.
* Stage 240 is the saved stub for
  `DiophantineConsistency.Sign17KWeightAggregateProbe`; it has no recorded
  dependency child, compile child, output or stage-240 log. The plan names
  `Sign17ExactDegree`, produced at stage 224, as its project import. The
  current candidate list shows its retained prefix object and two `Init`
  paths resolving to the same toolchain object. These are lexical/OS
  observations, not Lean dependency resolution.
* None of the **3,770** output suffix slots for the remaining 290 planned
  modules is present under the retained output root; the 13 final audit-client
  slots are also absent. All 39 stage-240 suffix slots across the retained,
  package and toolchain roots are absent. These observations do not cover all
  future imported module names, runtime file types or a future output root.

The precise counts, stage-240 paths and hashes are in
[`observation.json`](observation.json). The retained paths and files must
remain available to reproduce it; cached hashes and non-atomic reads can miss
intervening mutations. No claim is made about whether any absent companion is
needed, whether the monitored children had undetected short-lived activity, or
whether any unrecorded producer was compatible.

## What a separately engineered continuation would still have to establish

A continuation that reuses the prefix would need a separately reviewed,
fail-closed design that preserves retry05 evidence and fixes all inputs for the
full duration. In particular it must authenticate the selected Lean binary and
all package/toolchain and runtime providers and their transitive ancestry;
revalidate the prior base history and any implicit or companion files actually
used; and establish that retained prefix objects and their loaded companions
are mutually compatible with that exact environment. The 716 recorded direct
edges and matching hashes are meaningful evidence but do not by themselves
supply this closure.

It must define a distinct output/state arrangement without replacing the
failed root. Changing roots can change search precedence, realpaths, companion
lookup and generated state; the old direct-guard hashes cannot simply be
asserted to describe a new search path. A reviewed continuation needs to map
and recheck every selected producer, search candidate and required companion,
resolve collisions, and protect or revalidate inputs against mutation. It must
account for the pre-existing stage-240 stub without treating it as a passed
child, materialize or safely reference the remaining source snapshots, and
execute a fresh guarded dependency check and compile for **each of the 290
remaining planned stages**, then the final audit client. The pending audit
client requests the three endpoint/bridge/evaluation axiom reports. Its
postflight must cover both the reused prefix and the new outputs and compare
all intended routes and sources; it must independently review the final
state and axiom reports.

If any required prefix or provider evidence cannot be authenticated, rebuilding
the affected dependency closure in a fresh guarded build is the defensible
alternative; this inspection does not determine a minimum rebuild subset. A
full fresh replay remains 529 planned stages plus the audit client. Both
approaches must use the established exclusive Lean slot and resource guards;
free disk was below the 5,100,000,000-byte stop floor when this work began.
The recorded historical floor observation is not a resource reservation.
Even successful completion would establish only the audited formal statements
and provider boundary, with physical TeX/PDF association remaining separate.

Run read-only from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/current14-carrier65-retry05-prefix-feasibility/inspect.py | cmp - Computability/DiophantineConsistency/research/current14-carrier65-retry05-prefix-feasibility/observation.json
```
