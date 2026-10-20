# K-theory 222-state candidate

This binary, single-tape machine has **222 working states**, including initialization, plus
a separate halt state. It starts in state 0 at head 0 on an all-zero two-way infinite tape.
Every transition moves left or right. The complete 444-row table is [zfc_k222.tm](zfc_k222.tm).
**It is the smallest known candidate** whose blank-tape non-halting is equivalent to Con(ZFC).

The machine is ProveIt's own composition, made at the batch 181 intake. It stacks two
independent 223-state constructions that both start from the [224](../candidate-k224/README.md):

- **A**, [Source 127](../candidate-k223/README.md): the conditional K root, a helper allocation
  and the fold 18 → 180;
- **B**, Source 128 (and Source 130, which delivers the same machine): one equality row
  `G(a,b,c) = Eq(c,a) → (Eq(c,b) → ∀_{RelCode(a,b)} Eq(a,b))`, which replaces ρ7 and the
  separate equality helper, with the folds 303 → 118 and 302 → 159.

An ordinary mathematical proof, formalizable in ZFC, gives

  ZFC ⊢ (this machine does not halt from the blank tape ↔ Con(ZFC)),

by composing the two packages' arguments as explained below. **No Rocq or Lean theorem exists
for this table**, and no proof internal to PA. No absolute consistency, unconditional
non-halting, minimality, or two-sided independence from bare consistency is claimed.

## Why the two savings stack

**They change disjoint parts of the source.** Against the 224's source:

- A only moves one 27-leaf block inside the K core;
- B inserts its G row at the old ρ7 (leaf 486) and drops the helper from the bundle's tail.

Every subtree A changes is untouched by B. So A's changed subtrees graft onto B's source
([code/graft.py](code/graft.py)): 4,581 leaves, 186 distinct interior nodes, depth 38, zero
run 6.

**The emitted calculus is A's with B's rewrite.** [code/verify_ab_emitter.py](code/verify_ab_emitter.py)
runs the 224 package's pinned symbolic executor:

- the stacked AX bundle word emits exactly `And(Kc, RV)`, where Kc is A's conditional core
  `c → ¬∀c (b∈c → ¬H)` and RV the membership vacuity;
- the row emits G;
- the combined source's leaves are exactly A's, with these two word substitutions and no
  other change ([record](evidence/emitter_check.txt)).

**The calibration composes.** B's certificate proves that the G calculus and the
ρ7-plus-helper calculus have the same numerical theorems. Its rules are G, ρ1, ρ2, ρ6,
MP, GEN and classical tautologies, and its bundle step treats the K core as an opaque formula.
So it applies verbatim with A's conditional core: the stacked calculus has exactly A's
theorems, and A's conditional-K calibration (two markers and a hereditary domain, with the
restricted-helper interpretation) covers it.

**The table.** [code/stack_ab.py](code/stack_ab.py) starts from A's K-labelled table. It
recompiles only the changed source nodes, with the incremental compiler of B's
`construct_g226.py`:

- a dead single-role node's state is reused;
- leaf rows take the existing dispatch actions;
- every compound decoder entry is checked by tape simulation.

That gives 224 states, with 4 fresh and 22 reused. B's two source-dependent folds then
apply to the same nodes (B's fresh labels 303 and 302 are 301 and 135 here), and the result
has 222 states. In accounting terms it is 49 engine states + 186 nodes − 13 tag-shared roles:
B's node and A's sharing.

## Verification

| Check | Result |
| --- | --- |
| Direct unbounded runtime of **this table** on its own source, with Source 103's checker ([receipt](evidence/runtime222.json), [cases](evidence/runtime222_cases.json)) | `UNIVERSAL_MATHEMATICAL_PASS`: **5,956** guarded cases, **1,443,614** symbolic rules, all 444 rows, minimum instruction duration 13 |
| Exact blank startup, sparse and dense ([code/boot.py](code/boot.py), [record](evidence/boot.txt)) | the complete dispatch frame after **409,835** steps |
| Finite screen on every leaf and both decrement guards ([record](evidence/screen.txt)) | 0 failures |
| Exact emitter of the stacked source ([record](evidence/emitter_check.txt)) | `And(Kc, RV)` and G; leaves = A's with two substitutions |
| Canonical, inherited and K-label tables | the same machine (BFS-canonical forms equal) |

These are the intake's own checks. The runtime checker is the same adapted Source 103 checker as
for the 223s. The scripts in `code/` ran on the extracted packages of Sources 125, 127 and 128,
which are placed in the zfc-closure-kernels host; their paths are the intake's scratch paths.

## Exact files

| File | Meaning |
| --- | --- |
| [zfc_k222.tm](zfc_k222.tm) | Canonical table: states 0–221, start 0, dispatcher 22, halt 222. |
| [zfc_k222_old.tm](zfc_k222_old.tm) | fold241 inherited labels (start 95, dispatcher 96, halt 254), the table the checkers ran on. |
| [sites_logical.json](sites_logical.json) | Exact 4,581-leaf stacked source. |
| [ingredients/](ingredients/) | The K-labelled table, and the 224-state K-labelled table before B's two folds. |

Canonical SHA-256 `60e21a040e58e2a2840b0f3d58ad3ee0e6ef4d0d5cdf1372d5a69355f1198ca1`; inherited
`027b5e1cd5cae6cd158f9490021c13b0df395d8d7187739204d049b98236b06a`; source
`6e6a863fd475a7508e9afab8e76b5291bf0541b4b2999b71c6ecea5fcd41c3ae`.

See [ATTRIBUTION.md](ATTRIBUTION.md).
