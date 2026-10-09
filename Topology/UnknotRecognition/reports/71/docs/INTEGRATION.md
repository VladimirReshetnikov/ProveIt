# Proposed integration and geometric gate

## Placement

Place the delivered package as an additive research report under the location
assigned by ProveIt's incoming-report procedure. Do not overwrite the incoming
README or assign a report number in advance. The delivery contains no auto-applied
patch, and no remote repository file was changed.

The package is standalone. Its Python imports are resolved from `code/` when a
script is run directly. Tests add that directory to their import path. Production
namespace packaging can be introduced during native integration; no dependency on
a user-specific filesystem path is required.

## Existing destination, not a missing source bridge

The inspected `synthesis/diagram_exterior.tex` at revision
`66098968e88bba797143ac1bf7ad0ac4c5f697df` already supplies a native source-checked
compact knot-exterior construction. The pulling variant uses `20*max(1,n)`
tetrahedra for a validated one-component planar diagram. That source bridge is
not the missing theorem in this delivery.

The additional requirement is a complete, type-controlled disk-assembly search
in that exterior. Fast checking of a supplied normal surface and construction of
a source-certified exterior do not, by themselves, produce such a search.

## Admission contract for an experimental adapter

An adapter must export actual compact disk pieces and actual labelled boundary
intervals. Distinct intervals have disjoint endpoints and collars. Each live
component must meet the live interface, and every identification relevant to the
future must be represented. A named point port or a binary bundle of many normal
arcs is not automatically one interval.

All candidates reduced together must share an external geometric type. Every
admissible outside piece, arc identification, framing, boundary constraint, and
ambient-region condition must remain legal after replacing one candidate by
another of that type. In particular, a local option guarded by an unrecorded
same-component predicate is not admitted by the theorem.

The adapter supplies coarse past and future connectivity partitions. Either it
uses the explicit finite-grammar compiler or independently certifies that every
candidate refines `sigma` and every legal complementary cap refines `rho`.
Envelope safety must be proved from the actual source language; a correct local
matrix certificate cannot establish this premise by itself.

Each successful assembly must replay to a properly embedded disk in the same
source-certified exterior. Source torus cocycles, actual external boundary
chains, and their seam corrections must certify the nonzero terminal parity.
Generic two-bit labels in this prototype are only an algebraic interface.

## Suggested staged integration

**Stage A: read-only profiling.** Export explicit arc interfaces and safe
connectivity envelopes from small existing workloads. Record raw arc count,
blocks on each side, connectivity, cycle rank, number of types, and the costs of
producing that data. Do not prune native candidates yet.

**Stage B: shadow reduction.** Run the reducer on copies of one admissible typed
family, verify every certificate independently, and compare all known terminal
queries with the unpruned baseline. Shadow successes are not new native verdicts.

**Stage C: source-bound witness replay.** Bind one recovered abstract witness to
the native exterior, embedding data, normal or other geometric representation,
and essential-boundary certificate. Mutate source bindings and geometry to test
that unrelated witnesses are rejected.

**Stage D: opt-in production search.** Only after the preceding contracts are
proved and tested, use representative reduction in an explicit source language.
Preserve a fallback for inconclusive and resource-limited cases. Record whether
that language is complete for the intended class before interpreting exhaustion.

**Stage E: restricted-class complexity theorem.** Prove bounds on language
construction, types, cycle overlap, integer sizes, witness expansion, and replay.
The search contributes `poly(I,B)*2^(3*lambda_max)`; all other terms remain in the
end-to-end accounting. A general bound requires these obligations for all inputs,
not only for measured instances.

## Production API boundary

Useful standalone entry points are:

```python
from envelope_kernel import Candidate, Envelope, reduce_family
from checker import check_reduction, check_run
from grammar import Grammar, Patch, solve
```

`reduce_family` returns retained original indices and a source-bound expansion
certificate. Supply the **actual original family** independently to the checker.
Do not trust a source table bundled inside an otherwise untrusted certificate.
`check_run` regenerates the explicit grammar's candidates and validates every
stage; it is stronger than checking only a final positive witness.

Local certificate failure or an allocation guard means **not verified**. It is
not a proof that no disk exists. Do not translate `NO_DISK_IN_GRAMMAR` to
`KNOTTED` unless the geometric language is certified complete. Do not translate
`FOUND_ABSTRACT_DISK` to `UNKNOT` without embeddedness, source binding, and
essential boundary.

## Adaptive restrictions

Narrowing the future language preserves an already valid representative family.
Widening it may require candidates previously discarded; recover the unpruned
source or an adequate persisted provenance structure before widening.

Filtering past candidates after reduction is a different operation. Simply
filtering the retained subset can remove the only replacement for an eligible
source candidate. Rebuild from the eligible original family or prove that all
needed replacements survive. Account for rebuilding and retained provenance.

## Required native validation before a speed claim

Use paired measurements with identical preprocessing, option lists, validation,
resource budgets, and final verdict semantics. Include envelope construction,
type splitting, certificate generation/checking, and witness recovery according
to a disclosed common timing policy. Compare against the maintained recognizer,
not only against the supplied abstract baseline. Preserve negative controls and
report slowdowns as well as gains.

No native integration, native regression run, or native timing experiment was
performed in this delivery. The abstract examples are not knot inputs.
