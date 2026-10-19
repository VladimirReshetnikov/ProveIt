# Intake 173: Sources 104–109

Placement `197ce3dc67`; arrivals `1cba633ec3` (Source 104) and `ec480205a1`
(Sources 105–109). Every package reads ProveIt at `ce19293937` and takes the batch-172
packages as inputs. Each main `report.tex`, its PDF and the delivery README are
archive-only; the other members are mapped in
[the placement map](data/intake173-placement.json), with the prefixes below. The
common 238-state table, canonical `909f29c4…` and inherited `ab1f12ce…`, is
[`candidate-combined238`](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-combined238/README.md).

<a id="source-104"></a>
## Source 104 — `ZFC238_Research_2026-10-19.zip` (prefix `104-res238-`)

- **Machine:** the common 238 table. It is constructed from Sources 101 and 103, which
  it re-ships in full under `combine/`. It gives two unbounded routes: the direct
  runtime proof of the 238 table (8,386 cases, 2,255,513 rules), and the guard re-proved
  on the changed source with local transfer. An independent boot-alignment checker
  compares whole tapes at all 409,685 matched local-block checkpoints (old/new lengths
  409,691/409,835).
- **921-bit equational packet:** the 946-bit packet of Source 101 minus its explicit
  truth equation, which follows from the retained Sh1, class-NAND and arbitrary-witness
  equations; an all-algebra argument is included. **No state count.**
- **Displaced-head quotient search** on the 238 table (`encoding/`). It allows a ±2 head
  representation and two synthesized retained rows, in an eleven-cell window with old
  and new step limits of 63 and 127. **No survivor** across 45,741 ordered candidates.
  This is negative within that class, not a lower bound.
- **Non-claims:** no Lean/Rocq theorem for the 238 table; no minimality or priority. The
  two unbounded routes share one engine, so they are complementary rather than
  independent kernels.

<a id="source-105"></a>
## Source 105 — `ZFC238_Construction_2026-10-19.zip` (prefix `105-con238-`)

- **Machine:** the common 238 table. The guard is re-checked on the changed boundary
  source, and a direct runtime proof covers the final table.
- **A broader source-associativity criterion.** Reassociation of three chunks is valid
  whenever the first has no escaping break and the third no escaping continue; the
  middle is arbitrary. The exact control graph, including all 8,386 guarded targets, is
  preserved. Source 103's rule was narrower: all three chunks closed.
- **A depth-39 source.** A bounded search lowers the maximum path depth from 48 to 39,
  keeping 224 distinct subtrees, 6,455 instruction occurrences and maximum zero-run 6.
  **No 223-node source was found** in that search. The depth-39 source is not compiled
  into a machine.
- **Fourth logical input.** Two finite matrices cover every finite implication term in
  the other three inputs, falsity and truth, with no depth bound, so Peirce's law cannot
  be recovered by any such replacement. A colored expansion of a ZFC set model extends
  the obstruction, conditionally, to the full CP/GIC bundle for compound terms and the
  leaves `b`, `c`, falsity and truth. The bare leaf `a` stays open. These are
  non-derivability results, not inequiconsistency results or lower bounds.
- **Non-claims:** no consistency, unconditional non-halting, two-sided independence,
  minimality or kernel-checked 238 endpoint.

<a id="source-106"></a>
## Source 106 — `ZFC_237_State_Construction_2026-10-19.zip` (prefix `106-fold237-`)

- **Machines:** the common 238 table as the intermediate (`zfc_composed238*`), and the
  **237-state table**: canonical `7eda1da1…` (start 0, dispatcher 84, halt 237) and
  inherited `a3c4407f…` (95/96/254).
- **The fold:** delete 235 and merge it into 98, with `98/0 → 0 L 240`,
  `139/1, 156/1 → 1 R 98` and `240/1 → 1 L 87`. The three exceptional old steps become
  blocks of 3, 5 and 3 steps, and every intermediate write preserves the bit already
  present. An inductive predecessor invariant from state 95 holds on **every initial
  binary tape**, so no register-frame premise is needed. The clock is
  `τ(t) = t + 2a(t) + 4b(t) + 2c(t)`, with `t ≤ τ(t) ≤ 5t`. The invariant covers
  120,448 admitted state/window cases, and an independent review checks all 476 old-row
  implications. Startup is unchanged at 409,835 steps; the new rows are not used during
  it.
- **Direct runtime proof** of the 237 table: 8,386 cases, 2,261,369 rules, all 474 rows,
  minimum duration 13.
- **Discovery** (`discovery/`): Source 101's three C++ programs applied to the 238 table.
  The profile covers 33,545 runs and 27,995 state/window pairs; the joint search covers
  28,203 state pairs and 669,196,927 helper checks and finds **exactly one candidate**.
  An earlier run of the same family on Source 101's 239 table found nothing.
- **Non-claims:** no Lean/Rocq endpoint and no PA derivation for the 237 table; the
  calibration is inherited, not rebuilt; Python certificates are not proof-assistant
  certificates; no alternative frontend is claimed to beat 237 states.

<a id="source-107"></a>
## Source 107 — `zfc238-composition-20261019.zip` (prefix `107-comp238-`)

- **Machine:** the common 238 table. The guard is re-run on the changed source with a
  certified one-run constant of at least 23, where 2 suffices. Source 103's archive is
  re-shipped verbatim under `vendor/`.
- **713-bit equational packet** (`foundations/`): eight equations over 12 operation
  symbols and four variable slots. It uses a selected complemented witness: the
  constructor becomes existential negation, the old interface translates as
  `Q_old(a) = Q(P(a,a))`, and the witness as `W_old(s,a) = W(s,P(a,a))`. Intermediate
  packets have 917 bits (13 equations) and 745 bits (9 equations, with flag). The target
  is `N(d,d) = d`. Subject to the cited raw-EPSC/ZFC calibration, its non-derivability
  is equivalent to Con(ZFC) in ZFC. **Not compiled into a machine; no state count.**

<a id="source-108"></a>
## Source 108 — `ZFC238_Construction_2026-10-19 (1).zip` (prefix `108-con238b-`)

- **Machine:** the common 238 table. Its evidence includes a direct runtime proof
  (2,255,513 rules), the predecessor-guard runtime (2,247,513 rules), a four-path local
  fold with 474 commuting rows, and a 409,692-checkpoint relative startup.
- **Equality-free logical simplification.** On a nonempty domain, with `E` equivalence
  and `R` membership, assume `H1`, `H7`, first-coordinate membership congruence `H5` and
  global-image collection. Then the single collection matrix
  `θ(x,y;a,c) = E(y,a) ∧ R(c,y)` derives second-coordinate congruence `H3`. A quotient
  argument gives a smaller relational presentation equiconsistent with the native SIR
  theory. **The numeric proof engine is unchanged.** Deleting its `rho3` row would need a
  separate non-circular derivation or a new complete engine. This is recorded as a
  possible source-level saving, not a result.

<a id="source-109"></a>
## Source 109 — `ZFC_238_State_Construction_2026-10-19.zip` (prefix `109-st238-`)

- **Machine:** the common 238 table, ending its replay with `FULL_238_REPLAY_PASS`.
- **937-bit, 14-equation packet** (`research/stack937/`): three closure-witness functions
  share existing structural constructors. **No state count.**
- **A rejected 238 rotation** (`research/source_search/rejected_rotation/`), a different
  syntactic edit. It fails the universal instruction-frame specification, and the replay
  reproduces its exact tape discrepancy. It is kept as a negative control.
- **Non-claims:** no new kernel-checked endpoint, serialized ZFC derivation or internal
  PA theorem; the ancestor calibration was not rebuilt.
