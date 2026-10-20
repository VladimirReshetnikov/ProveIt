# Intake 181: three more 223s, and a stacked 222

Placement `5342a12e22` imports three packages as **Sources 128–130** and retires their ZIPs.
The host now reconciles **130 sources**; the collection remains **290 reports**. The
[placement map](data/intake181-placement.json) accounts for all 347 members:

- 209 staged byte-identical (5 at the host root);
- 126 exact aliases;
- 3 history aliases: each package vendors Source 125's archive (blob `a4b02ffe` of `49ee7cfdc8`);
- 9 archive-only (main manuscripts, PDFs, delivery READMEs).

## The four 223s compared

All four start from the [224](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k224/README.md).
Accounting is engine states + distinct interior source nodes − tag-shared roles:

| Source | Package | Idea | Leaves | Accounting |
| --- | --- | --- | ---: | --- |
| 127 | `K223_Construction` (`281af27565`) | conditional K root `m → ∃c (b∈c ∧ H)`; helper allocation; fold 18 → 180 | 4,799 | 49 + 187 − **13** |
| 128 | `K223_Construction (2)` (`1f751b0aa4`) | one equality row G replaces ρ7 and the helper; folds 303 → 118, 302 → 159 | 4,581 | 49 + **186** − 12 |
| 129 | `K223_Construction (3)` (`076445a266`) | seed presentation of the K root, repeating the closure's request | 4,962 | 49 + **186** − 12 |
| 130 | `K223_Construction_And_Research` (`6ab3e41e4d`) | Source 128's machine (same table `0d4eb8ff…`, same source) plus research | 4,581 | as 128 |

So there are **three distinct constructions**. Sources 128 and 129 save a source node, and
Source 127 saves a sharing:

- **Source 128 (G).** `G(a,b,c) = Eq(c,a) → (Eq(c,b) → ∀_{RelCode(a,b)} Eq(a,b))`. A 315-node
  certificate shows that the G calculus and the ρ7-plus-helper calculus prove the same numerical
  theorems; it uses only G, ρ1, ρ2, ρ6, MP, GEN and classical tautologies. One closed rotation
  keeps the zero run at six, the source compiles to a 226-state parent, and three folds give
  223.
- **Source 129 (seed root).** It emits K's seed (witness-request) presentation, already
  calibrated in Elliot Glazer's development. The repeated request creates a shared subtree:
  209 distinct subtrees in place of 210, with all 12 contextual aliases kept.
- **Source 130** adds:
  - an alternative 224 with symmetric equality;
  - a negated-matrix K presentation that halves the negation macros but did not save a state;
  - a finite-only 229 polarity specimen;
  - logical counterinterpretations.

**Intake replays** (Source 103's adapted checkers, on tables relabelled from the delivered K
labels):

| Source | Screen | Startup | Unbounded runtime |
| --- | --- | --- | --- |
| 128 | 0 of 5,956 failed | exact, 409,835 | `UNIVERSAL_MATHEMATICAL_PASS`, 5,956 cases, 1,431,799 rules, 446 rows |
| 129 | 0 of 6,449 failed | exact, 409,835 | `UNIVERSAL_MATHEMATICAL_PASS`, 6,449 cases, 1,566,562 rules, 446 rows |

## Stacking: a 222

Where each source differs from the 224's:

- **127 and 128 change disjoint regions.** Source 127 moves one 27-leaf block inside the K core;
  Source 128 inserts G at the old ρ7 and drops the helper from the bundle's tail. Every subtree
  127 changes is untouched by 128.
- **127 and 129 both rewrite the K root**, so they are alternatives.
- **128 and 129 both rewrite the bundle's tail.** Source 129 even changes that block's leaf
  sequence, so 128's node rewrite (lowering its helper node `q(224)`) finds nothing to act on.
  Calibrated on the 224, the same rewrite reproduces Source 128's source byte for byte. Stacking
  these two would need a newly designed emitter.

The intake stacked **127 with 128**. The result is the
[222-state candidate](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k222/README.md),
49 + 186 − 13:

1. **Source.** Graft 127's changed subtrees onto 128's source: 4,581 leaves, 186 interior
   nodes, depth 38, zero run 6.
2. **Emitter.** The 224 package's pinned symbolic executor confirms the stacked emission:
   - the bundle is `And(Kc, RV)`, with Kc Source 127's conditional core;
   - the row is G;
   - the leaves are 127's, with exactly the two word substitutions.
3. **Calibration.** Source 128's equivalence never uses the K core, so it holds with the
   conditional core. The stacked calculus has exactly Source 127's theorems, and Source 127's
   conditional-K calibration covers it.
4. **Table.** Start from 127's K-labelled table and recompile only the changed nodes with
   128's incremental compiler (4 fresh states, 22 reused, every compound entry
   tape-checked): 224 states. Then apply 128's two source-dependent folds to the same nodes:
   222 states.
5. **Checks.**
   - runtime: `UNIVERSAL_MATHEMATICAL_PASS`, 5,956 cases, 1,443,614 rules, all 444 rows;
   - startup: exact, 409,835 steps;
   - screen: 0 failures.

Open: whether 128 and 129 can be stacked with a new emitter, which would reach 185 nodes.

## Formal status

No proof assistant checks any of these tables. The 222's logic is the same as the 223 of
Source 127, so its Rocq obligations are those listed in [intake 180](intake-180.md#formal-status):
soundness through Elliot's decoder and the conditional-K interpretation. To them it adds the
G equivalence (Source 128's 315-node certificate, at the code level).

## Non-claims

No proof-assistant theorem for any table here. No PA endpoint. No minimality.

## Attribution

The theory K and the 230-state machine are Elliot Glazer's. The constructions of Sources
127–130 are their own; the composition of 127 with 128 is the intake's.
