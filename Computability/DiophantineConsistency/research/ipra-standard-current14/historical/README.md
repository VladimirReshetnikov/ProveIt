# Paired historical 14-variable endpoint: prepared, not run

This workflow extends the authenticated historical AQ29 project pair with the
16 source modules of the recorded single-author current-14 endpoint run. Its
fixed policy pins every source path, hash, declared import and per-module
axiom-report name: the final module has four reports and the other 15 have
none. The policy is compared by the toy controls with the independently
recorded [author additions](../author-additions.json). The planner explicitly
targets all 16 modules, including any outside the endpoint dependency closure.
The preparer and both sibling builders enforce the report policy and allow
only the recorded Lean metatheory axioms; equal forged sibling reports do not
satisfy the pinned names.

The [toy controls](control-receipt.json) cover source/Git drift, immutable
policy and per-module reports, unobserved parent exits, output companions,
sibling hardlinks, protected Foundation/toolchain roots, a paired real-Lean
fixture, and a complete observed parent/freezer/extension fixture. These use
synthetic inputs and providers; they do not prove the current14 endpoint. The
first adaptation of the immutable-policy control assumed a nonterminal report;
the current14 policy has none, so the test was corrected to mutate a silent
nonterminal module and the terminal report independently before the recorded
successful run.

The separately recorded [policy/log preflight](policy-preflight-receipt.json)
compares every module's pinned report list with its preserved historical
author log; the actual process exit is in
[policy-preflight-observation.json](policy-preflight-observation.json). This
preflight is not an independent external audit or a Lean replay.

The freezer and preparer authenticate the original matched parent pair and
its actual observed coordinator exit, preserve the complete ordered 1,210
source prefix, verify historical Git blobs and copy separate sibling object
seeds. Each sibling compiles all 16 additions in its own overlay. The
comparison checks sources, objects, reports, direct inputs and companion
identities. A manifest-only survey uses 984 parent dependencies, but the
other 226 rows remain part of the authenticated parent and seed inventories.

No real extension has been frozen or run by this workflow. **Do not launch
until an independent reviewer has audited this workflow and its fixed policy.**
The [runbook](REAL-RUN.md) also requires the prior independent parent audit,
its observed exit and pinned receipt, and independently rechecks the matched
parent. Historical basis, missing outer Foundation-wrapper exit, and
package-transitive, dynamic-load and transient-mutation limitations remain.
A paired build would not itself be a formal interpretation of the current PDF
or identify every possible ZFC consistency coding.
