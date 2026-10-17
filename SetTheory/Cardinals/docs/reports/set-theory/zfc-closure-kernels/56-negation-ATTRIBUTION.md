# Attribution and source boundaries

This packet is a research contribution based on ProveIt commit
`43026ff42f0939f09b9e95495248cfadcad38e38` (17 October 2026).

## Existing work

- **Mira-Cult** designed and built the original 254-state machine.
- **Jeff (`jeff87654`)** supplied the upstream Coq verification.
- **Andrew James Wade** supplied the public compiler framework under the
  retained MIT-0 `LICENSE.wade`.
- **mira-emmy** supplied the public 253-state adjustment cited in the
  baseline's existing provenance, PR20 head
  `0d544f2a2e3c18f12278441a74b7879f31cbe856`.
- **Vladimir Reshetnikov and ProveIt contributors** supplied the permutation
  candidate, Lean development and calibration, source recovery, and the
  prior research drivers and search ledgers used here.
- **Michael Karr**, *Affine relationships among variables of a program*,
  Acta Informatica 6 (1976), 133–151, DOI 10.1007/BF00268497, is the classical
  source for affine-relation analysis. The method itself is not claimed as
  a new algorithm in this report.

The `source/ProveIt/` subset preserves its source bytes. The copies under
`work/compiler_reduction/source27/` retain the original source-27 programs
under shorter sibling names needed by the experimental driver. Existing
Lean files used in the endpoint audit are preserved in
`work/theory_audit/upstream/`. Their repository and upstream pins are
recorded in the report and provenance JSON.

## New material in this contribution

The report, negation-constructor identities and clean macro rewrites,
whole-source affine certificate producer and independent verifier,
additional contract matchers and searches, modified-source machine audits,
context-aware compiler experiments, accepted fold sequences, and the
integration/verification harness were prepared for this task. General
methods such as affine invariants, ranked stuttering, and closed-sequence
reassociation are attributed to prior work; the report identifies the
concrete new applications and finite results.

## Licensing boundaries retained

`LICENSE.proveit` is an unchanged copy of ProveIt's MIT No Attribution
license for its own materials. The original upstream snapshot is explicitly
excluded from that blanket grant in its preserved
`source/ProveIt/lib/jeff-busy-beaver-zfc254/README.proveit.md`.
No upstream-wide license was declared in the pinned `busy-beaver` snapshot,
and this packet does not relicense it. Retained files and notices identify
their own provenance. The new contribution is intended for incorporation
under the destination repository's normal terms, without changing those
upstream boundaries.

The packet is generated research evidence, not a claim that the existing
252-state result or its formal verification was created in this session.
