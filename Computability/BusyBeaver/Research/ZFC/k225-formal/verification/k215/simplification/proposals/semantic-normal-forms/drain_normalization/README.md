# Kernel-checked drain normalization for the inherited K215 canonical graph

This component closes a specific gap in the earlier `affine-cores` proposal:
the universal drain induction, its finite-rank composition, and all literal
instance conditions are now Coq theorems. It is not a new Turing machine.

## Checked results

`DrainAffine.v` proves, without additional axioms:

* A drain testing register r, decrementing it on the nonzero self-loop, and
  adding c with c[r]=0 exits after exactly R[r]+1 graph transitions.
* Its exact output is F(R)[r]=d[r], and F(R)[j]=R[j]+R[r]*c[j]+d[j] for j!=r.
  In particular d[r] may be nonzero.
* Halting before and after this finite positive execution is equivalent.
* Any finite-fuel composition of recognized drain macros preserves halting.
* If drain exits strictly lower rank, fuel at least the starting rank reaches
  a non-drain node. Fuel counts whole macros, not graph or Turing steps.

`DrainInstances.v` contains the literal inherited graph and checks:

* 1,426 vertices; 1,059 recognized drain loops with complete list coverage;
* strict rank decrease and rank at most six;
* unique keys and complete target closure (missing lookup keys default to Stop,
  so this explicit check prevents unintended terminal transitions);
* one Stop, 367 retained vertices, and initial vertex 0 retained.

The concrete theorems `concrete_drain_contract`, `concrete_normalize_core`, and
`concrete_normalize_preserves_halting` apply to arbitrary nine-register vectors.
The generic module prints six closed assumption reports; the concrete instance
prints five. Both compiled with Coq 8.18.0, and recursive `coqchk` returned 0.
No proof objects or toolchain binaries are included.

## Exact scope

Normalization relates two configurations of the SAME canonical graph G.
This does not establish a new source-to-graph adequacy theorem, a separately
encoded 367-vertex matrix-machine equivalence, a binary runtime theorem,
a physical-state reduction, or a compilation speedup. The 1,059/367 discovery
and original graph are inherited from the prior affine-core packet. The new
contribution is the compiled theorem and concrete checked premises.

Registers are finite lists of natural numbers, so no functional extensionality
axiom is needed. Binary N control labels avoid expanding thousands of labels
into unary proof data; the numerical labels and graph edges remain exact.
An initial unary-label literal experiment exhausted its resource allowance
(exit 137); the successful binary-label build is the delivered version.

## Reproduce

With an installed Coq 8.18.0 and standard library:

```sh
python3 replay.py --coqc /path/to/coqc --coqchk /path/to/coqchk \
  --out /tmp/drain-check-fresh --recursive
```

Ordinary installations can omit the two executable arguments. Portable Coq
installations may require their usual COQLIB and OCAMLFIND_CONF environment.
The driver uses an empty build directory. It records every exit code, command,
log hash, and source hash. Do not infer logical validity from hashes alone.

To regenerate literal data:

```sh
python3 formal/generate_instances.py
```

The untrusted generator reads the exact shipped graph and rank JSON. The
resulting source is independently accepted by the kernel's finite checks;
its graph semantics are defined in `DrainAffine.v`. Graph encoding provenance
and the boundary still open to the source language are in `formal/input_binding.json`.

## Attribution

Input graph/rank data: ProveIt commit
56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3, under
Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/
simplification/proposals/affine-cores/structural/.

The earlier research supplied the 1,059-loop census and 367-core proposal.
This component adds the standalone Coq semantic proof, rank normalization,
literal instance generator/checks, and independent review. Retain the project
license and the distinction between inherited data and new formal results.
