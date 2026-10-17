# Removing the successful-MP dummy push

Removing the dummy truth push after a successful modus ponens comparison
shortens the expanded program by 19 instructions. It saves no states in the
two reconstructed compilers tested here. The optimized 252-state decoder has
not yet been tested with this source change.

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

The missing comparison is with the optimized decoder. Both tested compilers
allocate a decision state for each source DAG node. The maintained 252-state
constructor instead applies fixed patches and a register permutation to an
immutable table; it accepts no modified DAG. Running that constructor would
therefore reproduce the old machine while ignoring this edit. A meaningful
comparison needs an editable optimized decoder or a justified literal-table
patch. These two unchanged raw counts do not establish a lower bound.

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
