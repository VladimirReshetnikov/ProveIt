# Attribution and provenance

Prepared with ChatGPT for Vladimir Reshetnikov and the ProveIt project,
19 October 2026.

The original compact proof calculus, native set theory, register proof-search
program, and 254-state binary machine are attributed to **Mira-Cult**.
Upstream Rocq/Coq verification is attributed to **Jeff Ketchersid** and
contributors. The compiler framework is attributed to **Andrew James Wade**.
ProveIt and its earlier contributors retain credit for the logical
calibration, source, routing, initializer, transfer, decoder, and other state
reductions inherited by this work.

## Inputs

The inspected ProveIt checkout is pinned to commit
`ce192939372ac7944fe2a0208c68a96d49fb5e3b`. The three incoming 239-state archives
were added at commit `83fd3585484e5dffb37992f91f7dd4d3e70c437a`; their exact
file hashes appear in `PROVENANCE.json`. Their earlier source pin is
`13ec39ed43148b1807f51ed6e6528e1c84659562`.

The complete Boundary239 source certificate, source interface data, reference
tables, and the coordinated delayed-erasure reduction are inherited inputs.
Their original attribution statements are preserved at
`licenses/ATTRIBUTION-boundary239.md` and
`licenses/ATTRIBUTION-coordinated239.md`. Filenames and historical statements
inside these copies retain their original meaning.

`BusyBeaver239_Research_2026-10-19.zip` and
`ZFC239_Companion_2026-10-19.zip` contain the same coordinated-reuse table.
They are not counted as two different reductions. The other incoming
archive, `ZFC_239_State_Construction_2026-10-19.zip`, contributes the distinct
source/decoder saving called Boundary239 in this package.

## New contribution

This delivery contributes the specific compatible composition yielding the
literal 238-state table and the following new work:

- An exact, portable constructor and canonical renumbering with whole-tape
  sparse/dense startup agreement.
- A complete direct runtime replay on the exact new table and changed source.
- A separately implemented local symbolic simulation, predecessor-closure
  check, and whole-tape mapped startup audit.
- Fresh universal instrumentation establishing the delayed-erasure next-one
  guard on Boundary239's own transformed source.
- An independent dyadic-interval control and zero-padding frame audit.
- The explicit collection-derived membership-congruence theorem, relational
  quotient argument, and careful distinction from a numeric-engine deletion.
- The article, documentation, evidence assembly, and portable replay driver.

The underlying ideas of source associativity, tape-context sharing, delayed
erasure, and finite-list induction are not claimed as newly invented here.
The report makes no global historical-priority or state-minimality claim.

## Unchanged verification engine

`verification/symbolic_runtime.py` and
`verification/independent_runtime.py` are unchanged attributed incoming
engine/helper bytes, with SHA-256 respectively:

```text
c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145
0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346
```

Historical authorial comments inside these files refer to their original
work. The new wrappers select and pin the correct source and table without
changing the engine's transition or induction rules. Two runs through that
same engine are not two independently implemented universal proof checkers.
The local fold and interval/frame checkers are separate implementations.

## Terms and proof scope

Inherited licenses and notices are retained under `licenses/`; no inherited
material is relicensed. Newly generated material was prepared for the user's
requested incorporation into ProveIt, with no additional licensing
restrictions asserted.

The claim is the ordinary mathematical consistency-equivalence proof for
this explicit machine, using the identified inherited calibration, supported
by the supplied executable certificates. This package neither rebuilds the
ancestor formal proof library nor supplies a new compiled complete Lean/Rocq
endpoint for 238 states. It does not assert unconditional ZFC consistency or
two-sided independence from mere consistency alone.
