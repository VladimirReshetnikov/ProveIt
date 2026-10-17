# Removing the successful-MP dummy push

Removing the dummy truth push after a successful modus ponens comparison
shortens the expanded program by 19 instructions. It saves no states in the
two reconstructed compilers tested here. A later direct mapping into the
optimized decoder also retains 252 states; its changed blank entry remains
unresolved within one million steps. No new machine bound follows.

| Complete compiler | Original source | Modified source | Rows per machine |
| --- | ---: | ---: | ---: |
| Public Wade | 281 states | 281 states | 562 |
| Reconstructed Mira with compact initializer | 341 states | 341 states | 682 |

The [driver](mp_dummy_push_experiment.py) changes only node 130 of the
attributed `Dag254` program: its successful continuation goes to node 167
instead of node 166. This skips `pushwff` and retains the existing copy/restore
tail. All 219 reachable DAG nodes remain; expanded instruction sites fall
from 6,460 to 6,441. Formula constructors, logical rules, and both theory gates
remain present.

The intended MP success interface becomes `(TW, WS, D, H) = (B, S, B, 0)`
instead of `(B, P(0,S), B, 0)`. Accordingly, its proof compiler would remove
the last NIP from the final `[DROP0, NIP0, NIP0]` cleanup. These are source
changes with proof sketches, not checked Lean contracts. The experiment
provides no new consistency endpoint or machine bound.

The [record](results/mp-dummy-push-partial-cost.json) includes complete
initializers, exact table hashes, source hashes, and row comparisons. Each
backend changes one transition target. Both Wade runs reach the same complete
first root configuration after 39,769 moves. Both reconstructed Mira runs
pass their full source-site checks and reach the same complete initialized
configuration after 880 moves. The one undefined Wade row is explicitly
totalized by preserving the read symbol, moving right, and halting; this adds
one final head move to undefined-row halting.

The original raw-backend comparison did not cover the optimized decoder.
Both tested compilers
allocate a decision state for each source DAG node. The maintained 252-state
constructor instead applies fixed patches and a register permutation to an
immutable table; it accepts no modified DAG. Running that constructor would
therefore reproduce the old machine while ignoring this edit. The direct literal-table mapping below now supplies that previously missing
comparison for this one edit. These two unchanged raw counts do not establish
a lower bound.

Reproduce with an existing repository checkout and a fresh external directory:

```sh
python -B Computability/BusyBeaver/Research/ZFC/mp_dummy_push_experiment.py \
  --repo /path/to/Proofs --output /outside/fresh-output
```

The driver uses the vendored Mira-Cult/Jeff Ketchersid/Andrew James Wade
sources at upstream commit `297ab8df7e5de329605c3875b4934643b371a5e3` and
preserves the Wade backend's MIT-0 license in scratch. It reads the published
Coq program as data and runs no Coq or Lean build. The first run's final
provenance assertion confused the old-label and canonical 252-table hashes;
the successful second run corrected that assertion without changing the
numerical results. The frozen 252-state machine is unchanged.


## Exact mapping into the optimized decoder

The [portable mapping driver](mp_success_mapping.py) changes literal `Prog254`
row 6423's right edge from subtree 6434 to copying subtree 6453. It independently
regenerates a 2,998-pair segment relation to the modified 219-node DAG, whose
node 130 right edge changes 166→167. The
[changed literal rows, DAG and certificate](results/mp-success-mapping/results.json)
are retained. An [independent checker](results/mp-success-mapping-certificate-check.json)
validates every pair and all 5,994 successor edges; these are executable
checks rather than new Lean proofs. The original source-only MP compiler
repair and its pending contracts remain recorded in the prior cost evidence.

Actual frozen-table entry is a unique sequence of read-one transitions
`96→111→130→150→172→204`. Changing only old 204/read1 from `1 R113` to
`1 R132` bypasses the successful-MP push and enters its existing copy tail.
Shared state 113 still serves four other incoming contexts, so it is retained.
The [exact 504-row renumbering check](results/mp-success-canonical-alias.json)
maps this to canonical 202/read1, target111→130. These labels are derived from
the frozen table and its actual renumbering, independently of the reconstructed
compilers' labels. Every protected register-box row remains unchanged.

All 8,366 guard cases of the changed 6,441-leaf literal program pass the strict
affine diagnostic with fuel 1,000 per case, conditional on the four unchanged
register-box contracts. This tests the changed program's actual successor PCs.
All 252 working states remain syntactically reachable, and conservative exact-step
bisimulation refinement has only singleton classes. Those observations remove
no state; they are not a general minimality theorem.

The [whole-tape control](results/mp-success-structure/structure-and-boot.json)
finds the unmodified complete boot frame after 82,552 steps. The changed blank
run neither halts nor reaches that target within 1,000,000 steps. It also
reaches no observed empty-PC frame with gap at least 40, exactly one left
marker, and a whole parsed register file with at least nine blocks. The
patched row is used 20 times; the final observed state is old 85/head686 with
426 one-cells. Fuel exhaustion is unresolved and does not exclude every
possible legal dirty initializer.

```sh
python -B Computability/BusyBeaver/Research/ZFC/mp_success_mapping.py \
  --repo /path/to/Proofs --output /outside/fresh-mapping
python -B Computability/BusyBeaver/Research/ZFC/mp_success_structure.py \
  --repo /path/to/Proofs --mapping-output /outside/fresh-mapping \
  --output /outside/fresh-structure
```

The [portable replay record](results/mp-success-portable-verification.json)
compares 27 functional fields and all three source/certificate artifacts with
the original runs, preserves the original inputs, and records four argument
guard controls. Neither driver edits a maintained table or source, runs Lean
or Coq, or invokes a compiler. The
[publication record](results/mp-success-publication.json) keeps these controls,
independent review and retained artifacts separate. A proof of the changed
MP/compiler interface, a sufficient changed bootstrap and an actual state
reduction remain open; this bounded family is stopped here.

## Why removing the shared push globally fails

The copy tail at DAG node 167 adds its parameter to the current `TW`.
The leading push at node 166 saves `TW` on the stack and clears it first.
Skipping that push has the intended local effect when `TW=0`, as at the
successful MP continuation. It changes other callers with nonzero `TW`.

The [source context inventory](results/global-par1-contexts.json) links all
31 original `par1` occurrences to literal subtrees: 29 in axiom construction
and two in MP. Direct decoder paths for 24 occurrences cover all five incoming
rows of state 113. Seven further paths encounter earlier shortcuts and are
explicitly left unclassified.

The earlier MP call provides a concrete obstruction. In the valid working
state `(TW, WS, D, H) = (2, 0, 0, 36)`, test goal code `1`, which denotes
falsity. The original rule compares implication code `28` with cache `36`
and rejects. Skipping both MP pushes makes the earlier call add `2+1`
and use stack head `0`, producing implication code `36`. It then accepts
falsity. The initial top and cache have explicit theorem certificates:
`All(0, truth)` and `truth → Eq(0,0)`.

The [exact scalar calculation](results/global-par1-scalar-counterexample.json)
records both outputs and the unchanged cleanup sequence. This disproves
preservation of the old derivability invariant under the usual consistency
assumption; it does not assert that a changed blank execution reaches this
state. Restoring the earlier MP push retains another use of shared state 113.
The preserved historical audit scripts accompany the evidence; they record
their original paths and are not portable command-line entrypoints.
