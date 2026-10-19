# A 237-state binary Turing machine for ZFC consistency

**Primary result:** the explicit machine in `zfc_composed237.tm` has 237
working states, including its blank-tape initializer, and an ordinary
mathematical proof formalizable in ZFC establishes

\[
\mathrm{ZFC}\vdash
\bigl(\neg\operatorname{Halt}(M_{237},0^{\mathbb Z})
\leftrightarrow \operatorname{Con}(\mathrm{ZFC})\bigr).
\]

This is two states below the requested threshold of 239. It uses one
two-way infinite binary tape, starts on all zeros, and moves left or right
on every step. The 237 states include initialization and the entire
proof-search implementation. The separate halt outcome is not counted as
a working state. No prewritten input is required.

The main exposition is [report.pdf](report.pdf), with complete source in
[report.tex](report.tex) and `sections/`. Appendix A prints all 474
transition rows. The independently verified 238-state intermediate is
retained as a useful integration checkpoint.

## Exact machine identity

| Item | Primary canonical table | Inherited-label table |
|---|---|---|
| File | `zfc_composed237.tm` | `zfc_composed237_old.tm` |
| Working states | 0 through 236 | 237 sparse inherited labels |
| Start | 0 | 95 |
| Dispatcher | 84 | 96 |
| Separate halt outcome | 237 | 254 |
| Rows | 474 | 474 |

Canonical SHA-256:

```text
7eda1da1fcda629cae86d22b01d3faf419552cf04ed4179f0c045ad0adf2c1a6
```

Inherited-label SHA-256:

```text
a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a
```

The bijection is `renumbering.json`. The first line of each table is
`#! start <state>`. Each remaining line has the form
`state read_bit write_bit L_or_R target`. There are exactly two rows per
working state and no row for halt. A state name such as inherited 240 is
an ordinary working label; it is not the state count.

## What is new

The inspected incoming queue contained two distinct 239-state machines.
One removed inherited state 169 by coordinated runtime-helper reuse. The
other changed source-tree association and removed decoder state 218.
The first new result here is their verified composition into 238 states.
The compatibility proof re-establishes the runtime tape guard on the
changed source, rather than assuming that disjoint transition edits
automatically compose.

The next new result is a further fold from 238 to **237 states**. It
deletes inherited state 235, redirects its incoming edges to 98, and
changes two retained transition behaviors:

| Retained row | 238-state input | 237-state output |
|---|---|---|
| 98 / 0 | 0 R 113 | 0 L 240 |
| 139 / 1 | 1 R 235 | 1 R 98 |
| 156 / 1 | 1 R 235 | 1 R 98 |
| 240 / 1 | 1 R 99 | 1 L 87 |

The deleted rows are 235/0 = 0 R 231 and 235/1 = 1 R 16.
All 470 other retained rows are unchanged. The new paths reproduce the
three exceptional old steps in 3, 5, and 3 steps. Every intermediate write
preserves the bit already present. An inductive predecessor invariant
supplies all their guards, from state 95 on **every initial binary tape**.
The simulation has no additional register-frame premise. The exact clock
is `tau(t) = t + 2*a(t) + 4*b(t) + 2*c(t)`, with `t <= tau(t) <= 5*t`.
All 473 other old rows commute in one step through the state map.

This construction uses existing tape context to retain a control
distinction while sharing the actual control state. A coordinated change
to a helper return makes that sharing possible. See Section 5 of the
report for the complete local proof and `discovery/` for the search that
found it. The finite discovery profile is not used as a proof of a
reachable-context invariant.

## Proof scope and inherited calibration

The report gives an ordinary mathematical proof of the displayed ZFC
biconditional. It composes finite-table simulation, unbounded unary/list
induction, exact initialization, finite source-control isomorphism, and
the inherited source/calculus/ZFC calibration. The latter uses the actual
`CalibratedRotation240.halts_iff_zfc_refutation` theorem and the explicit
`LogicalSeed246.initial` source interface; it does not redefine ZFC
consistency by reference to the new machine.

The logical calibration is **inherited**, and its dependency closure is
cited rather than rebuilt in this archive. Selected relevant Lean files,
the exact source-data definitions, original explanatory notes, and the
independent mathematical review are retained in `reference/` and
`source_interface/`. The two repository pins and incoming archive hashes
are in `PROVENANCE.json`.

This archive supplies neither a new kernel-checked Lean/Rocq endpoint for
the 237-state table nor a serialized derivation internal to PA or ZFC.
Its Python certificates are mathematical checkers, not proof-assistant
certificates. The symbolic rules and the reason their verified contracts
imply the unbounded theorem are stated in the report.

No consistency assumption is needed for the equivalence itself. Actual
nonhalting follows under `Con(ZFC)`. Under the usual second-incompleteness
hypotheses, consistency then prevents ZFC from proving this nonhalting
statement. Bare consistency alone does not establish the additional
claim that ZFC cannot prove the machine halts.

## Verification evidence

| Check | Delivered result |
|---|---|
| Final literal table | 237 working states; 474 rows; complete canonical relabeling |
| Final direct runtime | All 8,386 guarded instruction cases; 2,261,369 symbolic rules; all 474 rows |
| Runtime parameter scope | Independent natural register values, arbitrary natural gap/first spare, arbitrary finite spare tail, complete zero tape exterior |
| Minimum actual instruction duration | 13 steps |
| Final local invariant | 120,448 admitted Boolean state/window cases |
| Independent local review | All 476 old-row invariant implications, by partial-assignment entailment; three open-tape blocks; 473 ordinary rows |
| Final blank initialization | 409,835 steps; all 409,836 checkpoints compared with the 238-state input; independent dense canonical execution |
| Source control | All 6,455 ordered leaf occurrences and 8,386 guarded descriptors; 13-stage rotation certificate plus independent graph audit |
| 238-state direct runtime | All 8,386 cases; 2,255,513 symbolic rules; all 476 rows |
| Composition compatibility guard | Boundary239: all 8,386 cases; 2,247,513 rules; all 478 rows; 32 explicit symbolic guard visits and six startup visits |

The final initialized frame has head -5, marker -6, header 176, logical
registers `(3,0,0,0,3,0,0,0,0)`, and 167 spare values all equal to 1. Its
351 one-cell positions are recorded exactly; every other cell is zero.
Initialization ends at inherited state 96, canonical state 84. The new
237-state exceptional rows are not used during this startup, so its clock
is unchanged from the 238-state intermediate.

The 8,386 runtime cases are finitely many **unbounded mathematical
interfaces**, not 8,386 small numerical executions. The 4,000-rule cap in
each symbolic case bounds proof construction, not machine running time,
register values, or spare-list length. Finite startup and discovery
experiments are identified separately from these universal contracts.

## Reproduce

Use Python 3.10 or newer with assertions enabled. The primary certificate
workflow uses only the standard library and does not require network
access, Lean, Rocq, or a C++ compiler.

```sh
python3 -B reproduce.py --output-dir replay
python3 -B reproduce.py --full --output-dir replay-full
```

The quick command verifies the manifest if present, reconstructs both
new tables, replays source-data/source-control/local/startup checks, and
audits all delivered full-runtime summaries and case records. It does not
rerun the unbounded runtime engine. The full command additionally reruns
the direct 238-state and 237-state runtime proofs and the boundary239
compatibility-guard proof, and compares their deterministic proof data
with the delivered records. Full replay takes several minutes on a
typical CPU; exact timings are not part of the claim.

The driver runs in a fresh temporary copy, preserves the original
evidence, and writes command logs and `replay.json` to the requested
directory. It rejects failed, partial, missing, or mismatched certificates
and refuses Python's `-O`/`-OO` modes. The two table constructors and the
individual checks can also be inspected or executed separately.

Build the PDF from this directory with a standard TeX Live installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The optional discovery search under `discovery/` needs a C++17 compiler.
It is not a prerequisite for validating the accepted machine.

## Contents and integration

| Path | Purpose |
|---|---|
| `report.tex`, `report.pdf`, `sections/` | Main proof, alternatives, and full transition table |
| `zfc_composed237*.tm`, `renumbering.json` | Primary exact machine |
| `zfc_composed238*.tm`, `renumbering238.json` | Verified intermediate |
| `build_composed237.py`, `build_composed238.py` | Deterministic constructions |
| `reproduce.py`, `verify_bootstrap237.py` | Portable replay and independent final startup |
| `verification/` | Exact local, source, affine/list runtime, and guard checkers |
| `evidence/` | Complete successful records, including every universal case |
| `inputs/`, `source_certificate/`, `source_interface/` | Pinned input tables, source definitions, rotations, and seed extraction |
| `reference/` | Inherited proofs and calibration sources; independent reviews |
| `alternatives/equational946/` | Inherited finite equational packet, generators, reference rewrite search, notes, and attribution |
| `discovery/` | New fold's finite search input, programs, profile, logs, and receipt |
| `ATTRIBUTION.md`, `licenses/`, `PROVENANCE.json`, `SHA256SUMS` | Credit, licenses, source identities, and artifact integrity |

The repository can adopt the canonical table directly, or first integrate
the 238-state composition and then the small all-tape 237-state fold.
The strongest local next step is a kernel formalization of the explicit
three-block simulation, using the provided exact table hashes and state
map. For the preceding 238-state step, keep the source-dependent G169
guard as an explicit obligation. The direct complete runtime certificates
provide a second endpoint formalization route.

Alternative presentations are discussed in Section 7: raw closure
schemas, equality-free EPSC, a 946-bit finite equational packet, finite
class theory, alternate implicational bases, and universal interpreters.
The packet-size and axiom-count results are distinguished from full binary
state counts. No new alternative frontend is claimed to beat 237 states.

Prepared for Vladimir Reshetnikov, 19 October 2026. See `ATTRIBUTION.md` for
the earlier constructions and exact scope of the new contributions.
