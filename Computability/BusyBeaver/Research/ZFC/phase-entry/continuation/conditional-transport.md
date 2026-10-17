# A precise transport question for the actual dirty startup

The R252 mutant reaches a complete root frame c19 after15,963 literal blank
moves: state96, head3, header22, PC000, physical registers
`[3,1,0,0,2,0,0,0,2]`, and spares `[0,0,0,0,0,0,0,0,0,1]`.
Its logical record is
`D=(np,tw,ws,ac,p1,p2,s1,s2,pl)=(0,0,3,2,0,0,2,0,1)`.
The portable control first replays all15,963 transitions and checks the entire
tape against this repaint, including both blank exterior tails.

The logical seed has an existing interpretation. Code2 is `wal(0,0)`, obtained
by generalization from truth, and3 is `P(2,0)`. Thus D satisfies
[`DirtyProgram254.Safe`](../../../../Lean/BusyBeaver/ZFC/DirtyProgram254.lean)
using `Enum254.good_cons` and `good_zero`. Its checked `iter_halts_iff` yields:

```text
IterHalts Dag254.dag254 (L2.enc D) ↔ Code254.C254 Code254.F.
```

The checked [`DirtyRoot254.virtual`](../../../../Lean/BusyBeaver/ZFC/DirtyRoot254.lean)
definition sends D to `(0,0,3,0,0,0,0,0,11)`. Fetch and the first read select
operation4 with the remaining fields0, namely AX(c1,x0,y0,u0). These concrete
calculations use existing definitions; this particular instance has not been
separately compiled in Lean. It is distinct from the storage-tag conjecture
for other prepared continuations: D already contains safe formula data.

Let M251 be the exact502-row R252 table constructed by deleting old204 and
changing only old172/read1 to write1, right, target252. The remaining desired
binary comparison can be stated precisely:

```text
HaltsFrom M251 c19 ↔ IterHalts Dag254.dag254 (L2.enc D).
```

Together with a certified finite blank prefix, this would inherit the existing
external ZFC consistency calibration. This comparison is unproved. It must
cover both directions, actual controller behavior at gap19, and every later
use of the changed row. The existing dirty-register theorem does not prove
binary correctness at this spacing; the maintained binary contracts require40.
The source's maximum path depth34 does not by itself justify19 or34.

## Controlled binary forks

`controlled_fork.py` forks exactly c19 under the original252 table and the R252
mutant. It stops before the next changed incoming row, at a new complete root,
at halt, or after1 million moves. Both reach the cutoff at state131/head629
with488 one-cells and identical entire tapes. Neither reaches the changed row
or another complete root. This finite slow prefix therefore already occurs
under the unchanged table from the dirty, short-gap seed; it does not depend
on executing the changed transition again.

A third control repaints the same primary registers and all spares with gap40,
preserving the head and marker. Under the original table it also reaches the
1-million-move cutoff without a new root, changed-row encounter or halt,
ending at state109/head217 with434 one-cells. Equal elapsed move counts across
different tape spacings need not correspond to equal source-program progress.
The different endpoint is not a semantic divergence proof.

The [fresh replay record](../../results/phase-entry-controlled-fork-verification.json)
contains all initial/final one-cell sets, hashes and stop conditions. The helper
is a separate sixth source; the earlier five-source evidence remains unchanged.

```sh
python -B Computability/BusyBeaver/Research/ZFC/phase-entry/continuation/controlled_fork.py --repo /path/to/Proofs --output /outside/controlled-fork.json
```

This uses literal transitions throughout, with no box summaries or assumptions
about the short-gap source representation. No infinite loop, future avoidance
of the modified row, or251-state consistency result follows from the cutoff.
