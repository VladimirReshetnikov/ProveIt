# A checked affine core for the exact K215 source programs

This packet turns the earlier **affine-cores** research proposal into a focused
Coq/Rocq proof: the exact `Prog215.p215` and `DagPerm.dagPerm` programs both halt
exactly when one common core with **367 distinct control vertices** halts. The
statement holds for every natural-valued register file. The binary Turing
machine still has **215 working states**.

The earlier packet identified the 1,059 drain loops, the 367 retained vertices,
the graph, and the source addresses. Those discoveries are prior work. The new
contribution is the generic drain proof, the compositional contraction theorem,
the actual source-to-graph adequacy theorem, and kernel-checked bindings to both
literal source programs. `CURRENT_BINDING.json` records exact byte equality to
the production programs at repository commit
`56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3`.

## Exact statements

The principal concrete results in `K215GraphBinding.v` are:

```coq
p215_core_halts : forall R,
  RM.rm_halts Prog215.p215 ([], R) <->
  CoreContraction.core_halts 6 K215DrainData.k215 0%N R.

dagPerm_core_halts : forall R,
  RM.rm_halts DagPerm.dagPerm ([], R) <->
  CoreContraction.core_halts 6 K215DrainData.k215 0%N R.

p215_dagPerm_affine : forall R,
  RM.rm_halts Prog215.p215 ([], R) <->
  RM.rm_halts DagPerm.dagPerm ([], R).
```

The last statement is exactly the existing public source-correspondence
contract. `source_deps/K215F/Source215.v` supplies it under the existing public
name `K215F.Source215.p215_dagPerm`; `EndpointClient.v` checks that exact name
and type. This is a focused source proof. The complete machine-to-ZFC endpoints
`Correct215` and `CorrectDense215` are not rebuilt by this packet.

## Why the contraction is sound

A recognized node tests register `r`. Its nonzero branch returns to the same
node, decrements `r`, and adds a fixed natural vector `a` with `a[r] = 0`.
Its zero branch exits to another node and adds a vector `b`. From any register
file `R`, it reaches its exit after exactly `R[r] + 1` checkpoint transitions,
with final registers

```text
F(R)[r] = b[r]
F(R)[i] = R[i] + R[r] * a[i] + b[i]  (i different from r).
```

`DrainCore.drain_exact_steps` proves this by induction on the arbitrary natural
number `R[r]`. It includes the final zero test and applies the exit increments
only once. `drain_halts_iff` derives equivalence of halting before and after the
macro. No bounded sampling, register invariant, integer overflow assumption,
or functional-extensionality axiom is used.

The normalizer composes at most six recognized drains. The generic theorem
`normalize_halts_iff` is valid for every finite fuel, even on graphs whose
drain exits cycle. The concrete checks show that fuel six always reaches the
retained core for this graph. They also verify all 1,059 ranks, their strict
decrease, the domain of every successor, absence of duplicate vertices, the
367 retained vertices, and their unique halt vertex.

`CoreContraction.core_halts_iff` proves both directions for the accelerated
execution. Each core edge begins with an actual original test transition;
normalization follows that transition. For the difficult direction, a bounded
halting predicate supplies an induction measure. The original test consumes
one unit of budget, and every normalized drain preserves the remaining upper
bound. Consequently the contraction cannot insert divergence or erase an
infinite sequence of silent transitions.

`SourceGraphBridge.source_graph_halts_iff` binds the checkpoint graph to the
existing register-program semantics. The checker inspects the actual leaf at
each recorded address, checks its test register, executes both intervening
segments, compares every increment count, and checks implicit-zero equality of
the next address. The proof reuses the inherited `seg_run`, `seg_hn`, and
`hn_ipeq` lemmas. In particular, path arithmetic uses the full consumed path;
the proof never deletes physical tape cells or applies `break`/`continue` to an
arbitrarily shortened path.

## Checked data and provenance

The graph has 1,426 checkpoint nodes and 2,850 outgoing test branches. One halt
has no branches. There are 1,426 source addresses and 1,426 reference addresses;
the maximum depths used here are 46 and 177 bits. The existing lossless
`PathCodec` preserves both leading and trailing false bits.

`generate_data.py` and `generate_binding.py` produce untrusted Coq literals.
`verify_data_binding.py` is a separate parser that reconstructs the actual
printed graph, rank trees, and address trees without importing either
generator, and compares every value with the input artifacts. These Python
checks are useful provenance checks; the concrete Coq checker evaluations are
the logical evidence for source adequacy and contraction.

The only inherited compatibility modification is an import of the proved
`Compat818.v` aliases in `RMEquiv.v`. The original Rocq 9.1 source is retained
under `source_deps/originals/`. Both production program files are byte-identical
to the pinned repository. Inherited notices are under `licenses/`.

## Reproduce

Use Coq 8.18.0, the toolchain tested in this run:

```sh
python3 generate_data.py
python3 generate_binding.py
python3 verify_data_binding.py
python3 build.py
```

The build compiles all 17 project prerequisites from the delivered sources and
then independently runs recursive `coqchk` on the typed public-interface
client. It records source and object hashes, exact commands, raw compiler
logs, elapsed times, peak resident memory, assumption reports, and the final
exit codes in `verification/build.json`. `--skip-recursive` omits the separate
recursive check while retaining ordinary kernel checking during compilation.
The shared advisory lock permits safe coexistence with other proof builds.
Use `python3 build.py --batch-lock` to hold that lock across this entire focused
build when several long-running proof jobs share the machine; otherwise the
driver releases it after each compiler process. The receipt distinguishes
waiting for the lock from an active compiler.

## Verification in the delivered run

All 17 modules compiled successfully from the supplied sources using Coq
8.18.0. All 25 printed assumption reports were closed under the global
context, including both source/core equivalences, the common-source theorem,
the same-name public facade, and its typed client. Recursive
`coqchk -Q source_deps '' -silent EndpointClient` then exited successfully.

The fresh compiler processes took 92.585 seconds in total; the separate
recursive check took 440.022 seconds. The maximum resident set was 824,712 KiB
for compilation and 301,616 KiB for the recursive check. These are measurements
from one run, without time spent waiting for the shared lock. They are not a
comparison with a rebuilt production endpoint. The complete receipt, exact
commands, source and object hashes, and raw logs are in `verification/`.

## Interpretation of the result

The 367-node core is a smaller **semantic proof interface**, not a smaller TM.
It exposes transfer, copying, and clearing loops through one proved arithmetic
rule and permits future source variants to change those loop implementations
without requiring a one-to-one correspondence of their internal tests.

The new graph/rank and location sources total about 285 KB, which is larger
than the previously delivered 109,958-byte normalized certificate. No faster
compilation or smaller complete machine proof is claimed. For the current
pair, direct normalized equality remains sufficient; the added value here is
the checked common affine core and reusable all-register macro theorem. The
earlier claim of 33 shared homogeneous matrices is not needed by this proof:
the kernel checks compositions of the proved drain functions directly.
