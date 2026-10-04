# Independent audit of the five-signal constant clock

Audit date: 4 October 2026, UTC. Verdict: **accepted within the stated exact-model scope; no mathematical defect found**.

This is a new review of the frozen constant-clock continuation, not an execution of its checker and not a claim that its entire frozen dependency has been independently formalized. The dependency's primitive durations, test sums, instruction assembly, and admitted encoded-state guards were read and reconstructed. The new padding's full local implementation, chronology, guards, accounting, and composition were checked independently.

## 1. Exact source identity and review boundary

Reviewed source roots:

- `/workspace/shared/five-signal-constant-clock-20261004`
- `/workspace/shared/five-signal-branching64-20261004`

Binding digests:

| Object | SHA-256 |
|---|---|
| Clock `PROOF.md` | `00cac79979a17bb5f803b9e0ff97bde2ec1039b1544a4991406f32cb9a08885a` |
| Clock `MANIFEST.json` | `1bca064140e6aa5827e8d727ffe491987e8cc4cbcf7e731aae1975a99fe486f1` |
| Branching64 `PROOF.md` | `85f5de45c0a30f8bdf45b82a613ef9e5a8c766b5d8215d17a3ebbbd0f60b370f` |

The audit verifies every listed member of both original manifests. Files not needed scientifically are read only as inert hash bytes. No original checker, author/upstream scientific program, physical simulator, saved collision schedule, or proof assistant was run. The original clock checker was read as text; its saved success output was not treated as a proof.

The new `check_constant_clock.py` was displayed and inspected before execution. It uses only Python's standard library and exact rational arithmetic. It parses the frozen prose tables, reconstructs duration formulas, and instantiates a finite symbolic local-rule certificate. It never evolves a physical configuration, chooses a next collision, or searches for a schedule. Its local word rows are fresh algebraic certificates, not stored simulation trajectories. Mathematical chronology arguments remain necessary and are supplied below.

## 2. Six output-coordinate core times

Source: branching64 §§2.3–2.4, 4.2, 5, 6, and 7; clock §§2–2.1.

The seven forward Z-flight durations sum to `25(2t+s)/18`. The six N-flight durations sum to `125t/9`. The physical inverse uses the same elapsed time and the same number of events, including a fresh terminal anchor bounce. Thus the nondestructive tests have durations `25(2t+s)/9` and `250t/9`, and counts 14 and 12.

An anchored scaling by `h` has duration `2(1+h)t`. A translation by `eD`, applied at entering target `u`, has duration `2[u+u/(1-e)]+2D`. Consequently:

- Increment: scaling by 1/2, then translation by D/40, costs `2D+(196/39)t`
- Decrement: scaling by 2, then translation by −D/20, costs `2D+(290/21)t`
- Positive conditional plus decrement costs `2D+(2620/63)t`

For A, the output inverses are `t=2x′−D/20` for increment and `t=x′/2+D/40` for positive decrement. For B, the distance from R is `r=39D/20−2y′` or `r=21D/40−y′/2`, respectively. The two B transfers add exactly 2D and six events. The B zero test uses target `D−y′` and spectator `D−x′`.

These substitutions give the following independent reconstruction. Every coordinate on the right is an **output** coordinate.

| Branch | Core duration | Core collisions |
|---|---|---:|
| A increment | `(341/195)D+(392/39)x′` | 14 |
| A zero | `(50/9)x′+(25/9)y′` | 14 |
| A positive decrement | `(383/126)D+(1310/63)x′` | 26 |
| B increment | `(69/5)D−(392/39)y′` | 20 |
| B zero | `(31/3)D−(25/9)x′−(50/9)y′` | 20 |
| B positive decrement | `(155/6)D−(1310/63)y′` | 32 |

The checker verifies the inverse coordinate substitutions against the forward updates and compares all six reconstructed rows and counts to the frozen table. There is no substitution of input geometry for the stationary geometry that padding actually receives.

The core's guards remain branch-specific. This review does not extend a zero or positive core to inadmissible sections. The encoding has `D/20<x≤3D/20` and `17D/20≤y<19D/20`. On zero A, the two test inequalities have margins at least D/4; on positive A, `y−8x≥D/20`. Reflection gives the same result for B. The increment/decrement, scaled, hidden translation, and final endpoints are strictly between their anchor and spectator on closed supersets of the admitted encoded bands; exact rational vertex certificates are retained.

## 3. All stationary words and their exact guard

Source: clock §§3–3.2. Put `a=x>0`, `b=y−x>0`, `c=D−y>0`. Each contact word below excludes departure and includes its terminal contact.

| Primitive | Contacts | Successive lengths | Event count |
|---|---|---|---:|
| LX | X,L | a,a | 2 |
| LY | X,Y,X,L | a,b,b,a | 4 |
| RX | Y,X,Y,R | c,b,b,c | 4 |
| RY | Y,R | c,c | 2 |
| LR | X,Y,R | a,b,c | 3 |
| RL | Y,X,L | c,b,a | 3 |
| Full loop | X,Y,R,Y,X,L | a,b,c,c,b,a | 6 |

For magnitude `v>0`, each length divided by v is a positive flight duration. Every flight connects adjacent stationary markers, and the checker verifies its signed displacement equals the specified fixed messenger speed times that duration. There can be no intervening contact: the messenger crosses precisely one open gap, whose interior contains no stationary signal. At a spectator crossing the direction persists; at the chosen target the outward phase changes to the inward phase; at a terminal anchor it changes to the next occurrence's departure phase.

At each marker, the three distances to the other markers are positive nonzero sums of a,b,c. This excludes triple contact. There is only one moving signal, so disjoint simultaneous contacts cannot occur. The four stationary signals cannot meet one another. Identity spectator crossings remain real binary contacts and are counted.

Therefore the exact padding guard is the entire strict ordered section `0<x<y<D`. There is no extra threshold depending on counter values or padding speeds. Conversely, every boundary gap a, b, or c occurs in the mandatory full-span loop, and its collapse also violates the strict stationary section. Boundary or reordered configurations are not admitted by this interface.

## 4. Local rules, real entry, joins, and finite control

Source: clock §§3.1, 4, and 6.

Each occurrence uses fresh outward/inward labels with speeds of opposite signs and common magnitude. Its target bounce replaces outward with inward. Its terminal anchor replaces inward with the next occurrence's departure label. Every intervening marker has both identity crossing rules. Each one-way transfer has one phase, two spectator identities, and a destination rule selecting the next departure phase. All rules consume and emit one messenger and the same literal stationary marker label; the nonzero messenger speed is distinct from marker speed 0 on both sides.

The independent certificate instantiates all six padding templates: **136 distinct local rules**, one for each counted padding-contact occurrence, with **58 messenger labels including six illustrative next-instruction labels**. These audit counts describe the template witness, not a claim about a program's minimal label count. Its rules are deterministic. Every listed contact is checked against the independently instantiated schema. Every phase join is at the same physical endpoint, and its next flight has positive length. No rule is used at departure as an extra zero-time event.

In particular, the original core's last L contact emits the fresh padding-entry phase at the **same +1 speed**. Padding first performs a full unit-speed loop, consuming 2D and six contacts. Only its fresh terminal L bounce chooses an arbitrary new magnitude. This legally implements the inherited outgoing +1 section; it does not overwrite a speed remotely. This initial loop is distinct from the two unit-speed transfers, which cost a further 2D and six contacts.

Fresh instruction/branch/occurrence names ensure that two program contexts do not share an ambiguous input. The original conditional has already acquired its zero/positive branch in finite labels; separate padding copies preserve that choice and the selected destination instruction until the final full-loop L bounce emits `Q_j`. The padding never re-tests an elapsed-time condition.

For any fixed finite program, finitely many such copies suffice, with the same numerical speed set independently of initial counter values and D. Identity completion on unspecified finite distinct-speed label sets stays finite and cardinality preserving. It cannot introduce extra contacts along the certified executions, because those contacts have already been excluded geometrically. This is a finite-table construction for a fixed source program, not an unencoded universal-program interpreter claim.

## 5. Exact complement and accounting

Source: clock §§4–5.2.

For a core row `αD+βx+γy`, take left coefficients `max(−β,0), max(−γ,0)` and right coefficients `max(β,0), max(γ,0)`. With `k=30−α−max(β,0)−max(γ,0)−4`, the padding is

`(4+k)D + max(−β,0)x + max(−γ,0)y + max(β,0)(D−x) + max(γ,0)(D−y)`.

This is exactly `30D−T_core`. Each nonzero target coefficient q is realized by a round trip at magnitude `2/q`; the final full-span loop has magnitude `2/k`. The first full loop and two transfers provide the fixed 4D. No signed negative wait appears. This also proves the general lemma for any rational C satisfying its strict sufficient bound, with C substituted for 30.

| Branch | k | Padding events | Combined events |
|---|---:|---:|---:|
| A increment | 71/5 | 22 | 36 |
| A zero | 53/3 | 24 | 38 |
| A positive | 13/6 | 22 | 48 |
| B increment | 61/5 | 22 | 42 |
| B zero | 47/3 | 24 | 44 |
| B positive | 1/6 | 22 | 54 |

All residual k values are strictly positive, including the tightest displayed row, B positive with k=1/6. The generic padding bound is 26: eighteen fixed contacts plus at most two target loops of four contacts each. The six actual templates use at most 24 padding contacts, and their maximum combined count is **54**, realized by a B-positive instruction. The coarser 58 bound is unnecessary but valid.

The ten added positive magnitudes are `39/196,18/25,9/25,63/655,10/71,6/53,12/13,10/61,6/47,12`. They are pairwise distinct and disjoint from the nine frozen core magnitudes. Adding their negatives and the stationary speed gives exactly **39 elements in the specified common sufficient speed set**. This is not a lower bound, and a particular source program may use a subset.

The core's final collision is counted only in the core. The padding then begins with a positive flight to X. Within padding each terminal anchor is counted once and emits the next phase. The new certificate checks 136 padding contacts in total across the six branch templates, whose sums are 22+24+22+22+24+22.

## 6. Identity, clock induction, and halting limits

Source: clock §§6–7.

All four stationary marker positions and their literal labels remain unchanged during padding. Hence D and the exact output coordinates x′,y′ are unchanged. There is no renormalization, shift, approximation, inverse counter update, temporary marker, sixth signal, or extra clock signal. Each binary rule preserves two live signals; combined with the untouched three, the live population is exactly five, including outgoing strands at contacts.

The core restores an admitted encoded output. Padding restores that very same section with the next instruction's +1 label. Induction therefore gives instruction-section times `t_n=30nD` for each completed nonhalting transition, starting from t_0=0. The period is constant within a run, and scales with the fixed D; D=1 makes the numerical period 30. It is not a scale-independent period across arbitrary D.

For any fixed finite time horizon and D>0, only finitely many 30D instruction blocks can occur. Each has at most 54 positive-separated collisions, so no finite-time collision accumulation can occur, including within a block. All pre-halt positions stay in [0,D].

Halting means arrival at the designated full-section label `Q_H`. If reached after N transitions, that arrival occurs at 30ND. Optional +1 identity escape through X,Y,R adds exactly three **post-halt** collisions; these are not a 30D instruction transition. That escape convention preserves the population but eventually leaves the spatial interval. No global immobility, confinement after escape, or finite-collision behavior for a separate bounce convention is claimed.

## 7. Checked primary-source positioning

The following PDFs were independently opened and their relevant text inspected on 4 October 2026. This is a targeted precedence check, not an exhaustive literature review.

- [Durand-Lose, MCU 2004 / LNCS 3354 (2005), author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2004_MCU.pdf), §3, PDF pp.6–8: two fixed scale signals, one position signal per counter, and one instruction signal establish the substantive five-live-signal precedent. The paper also explicitly specializes to equal-cardinality rules. Its ordering can vary, and its zero counters lie beyond the unit marker. The continuation's caution against claiming first five-signal universality is warranted.
- [Durand-Lose and Emmanuel, Abstract Geometrical Computation 11 (2021)](https://arxiv.org/pdf/2106.11176), §4, PDF p.8, Fig.4 and associated rules: a signal travels to a border and back, and selected speeds produce a delay proportional to the bounded width. This directly supports the stated precedent for geometric bouncing delays. The wider paper concerns synchronization and accumulation via recursive structures. Its presence does not settle whether an earlier equivalent exact-clock compiler exists.
- [Durand-Lose, CiE 2006, author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2006_CiE.pdf), §2.2, PDF p.5: reversing signal speeds and reversing collision rules are established reversal principles, with conditions for a globally reversible machine. The new branch-tagged inverse gadget does not establish global reversibility after arbitrary completion.

No novelty, firstness, priority, exhaustive-search, population-optimality, speed-optimality, or time-optimality conclusion follows from this review. The frozen proof's restrained positioning is appropriate.

## 8. Replay, preservation, and evidence limits

`checks.json` is the independently produced exact certificate. `replay.stdout.json` records its successful run. `portable_replay.json` records a second run after moving the checker and complete source packets to a different temporary root, with working directory `/` and output external to both source roots. Its certificate was byte-identical. An attempted output inside a source root was rejected before writing.

The bundled `sources/clock` and `sources/core` are inert byte copies for portable replay. The original source paths remain authoritative for preservation. Replay with Python 3.9 or later:

```
python check_constant_clock.py \
  --clock-root sources/clock \
  --core-root sources/core \
  --output /an/external/directory/constant-clock-checks.json
```

Read the checker before running it. Do not run the scientific source scripts in the bundled packets. The checker uses those files only to confirm manifest hashes.

`source_baseline.json` records both original source trees after the initial inventory and before the new checker or portable replay. `source_after.json` and `preservation.json` establish unchanged object sets, byte hashes, modes, owners, sizes, inode identities, and nanosecond mtimes/ctimes from that recorded baseline. O_NOATIME reads and directory enumeration were used for the baseline, subsequent scientific reads, and final comparison. The first `ls/find` inventory preceded this baseline, so historical directory-atime invariance before that inventory is not claimed. No source timestamps were reset to manufacture preservation.

The certificate is supporting exact arithmetic and finite symbolic rule inspection, not a formal proof-assistant theorem. The human arguments about strict adjacency, finite namespaces, induction, and timing are part of the acceptance. The core dependency's full original chronology remains a dependency rather than a newly machine-formalized theorem. These limits do not reveal a defect in the clock refinement as stated.
