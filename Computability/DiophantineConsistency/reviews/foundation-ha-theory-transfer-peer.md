# Foundation HA theory transfer — independent peer review

26 October 2026. PASS; no requested source changes. Root authored the
64-line main and 47-line checks. Controller independently read both complete
files, the author receipt, and the relevant actual theory/context, GG,
Foundation-to-PAHF logical map, HA relative deduction and eight-semiring-axiom
interfaces before performing the fresh replay. Controller authored neither
this pair nor its logical/HA prerequisites; prior independent reviews of
several prerequisites are separate evidence.

`HA.Relative.discharge` performs induction on the actual finite assumption
list. At each successor it derives the implication by deduction, recursively
discharges the remaining list, and applies the genuine closed proof of the
removed assumption. The existing `Relative.mp` combines finite arithmetic
axiom lists. No assumption is silently turned into an arithmetic axiom, and
the proof neither requires distinct assumptions nor closes their free
variables. The duplicated context test retains variables 0 and 7.

`intuitionistic_theory` uses the actual Foundation finite proof context and
its subset witness into the embedded source theory. It maps the finite
logical derivation, obtains each corresponding source sentence, and applies
the supplied HA proof of that exact image. `classical_theory` first applies
the existing proof-tree GG translation, so its hypothesis about the HA
provability of every translated source axiom remains explicit. There is no
semantic completeness, unrestricted HA classical rule, or hidden claim that
an arbitrary theory embeds in HA.

The concrete `semiringTheory` is exactly the existing eight-element list,
not all of PeanoMinus or full arithmetic. Its image hypotheses are genuinely
discharged by `FoundationHAArithmetic.semiring_axiom`. The source-axiom and
source-conjunction checks exercise that concrete transfer. This packet does
not establish full arithmetic transfer, correspondence of the final target
sentences, or an HA proof of the desired consistency equivalence.

Frozen source SHA256s:

| File | SHA256 |
| --- | --- |
| FoundationHATheoryTransfer.lean | `e25cb43e446840f1cfebe1020ce7ec74a38a12b98bc76371d94e54fc6fc2fa50` |
| FoundationHATheoryTransferChecks.lean | `53158b2880e1645902d8e115b80e177ab5fd8efd9395f6ac863ecf82f4b338fb` |
| Author receipt | `f7c72e904c9e7ea62bd7dcf932adb6cde863fca4266d9b110a1aafdc84926520` |
| Author dependency metadata | `dd6acf14eefa4a14990303e965e949cba074b6b2482eb2164b804ce85ab837f6` |

Both targets were excluded from the reused cache and freshly compiled in
`/tmp/foundation-ha-theory-transfer-controller-peer-zhykxn3_/lib`, using
Lean 4.32.0 and `-M6000 -j1 -DElab.async=false`. The private overlay reused
93 source-authenticated prerequisite modules, including 76 Foundation
modules, and the accepted package/toolchain boundary. All 500 inherited
pin observations, each recorded prerequisite source/object, compiler,
current package identities and both target sources were checked before and
after execution. No shared object was replaced and no prerequisite closure
was freshly rebuilt. The sources stayed pinned while root advanced HEAD;
the final metadata records snapshot `312077c9f601490c105f4f055a6822e7f5f8bda3`.

The two successful calls took approximately 1.64 and 2.51 seconds. Main
diagnostics were empty. Both output objects are byte-identical to the
author's accepted objects: main
`650dd0cde439197d5f7b70c1b1df785290135b8e3495366a57271bfc41e014d6`,
checks `0e13233b53e90430b6362b73d3226d1e71ff90c29246aac9a75efb9ac3f69035`.
All seven axiom reports were read. Discharge, intuitionistic transfer and
the duplicate-open-context check use only `propext` and `Quot.sound`;
the four GG-composed reports additionally use existing `Classical.choice`.
No new axiom appears.

The first private metadata-preparation attempt stopped before any Lean
invocation because cached objects use both singular and list record
formats. The corrected driver normalizes those two authenticated formats;
the rejected preparation driver is retained. There was no failed Lean
invocation in this peer replay. No author driver or incoming archive program
was executed.

[Independent replay metadata](foundation-ha-theory-transfer-peer-replay.json)
has SHA256 `09f07c473ac8eda8420c3bb4bf8ea63865153935be34ac487c619913ac2a296d`.
It binds the full reused inventory, commands, private snapshots, logs,
objects, compiler/package identities and the independently authored driver.
