# Bounded local search on the maintained 65-operation graph

This search found **no smaller graph in the enumerated local families**. It
does not establish a minimum, rule out other transformations, or prove any
new Lean theorem. The current equation and all existing files are unchanged.

The wrapper runs four functions from the existing pinned
`p64-qcube79-local-rewrite-search/search.py` engine against the actual current
candidate's hash-pinned 65-row graph. It uses the existing metric: binary
integer addition, subtraction, or multiplication costs one, and fixed integer
leaves cost zero. The graph has 14 positive integer inputs; the procedure does
not alter their domain. The search is for equal polynomial intermediates,
which is stronger than equality of positive zero sets.

For each graph target, it enumerates a replacement by one or two binary gates
using earlier graph nodes and integer literals 0–4; in the two-gate case the
second gate uses the fresh first intermediate, including its square. It
keeps a hit only if recomputing output liveness gives fewer than 65 gates.
It additionally checks an earlier-node/literal alias and a one-subtraction
replacement with negated value when all immediate uses square that target.
These last two checks are run for the port-uniform sample only.

There are two exact-target modular screens. In the first, the 14 variables
and four ports are independently sampled at three deterministic assignments
modulo 1,000,000,007. In the second, the fixed ports come from the actual
current gzip payloads after verification of both compressed and raw SHA-256
hashes; the witnesses have the same samples. Each pass covers all 65 targets,
442,585 first-gate constructions and 14,235 second-gate queries. The square
branch has 144 queries in the uniform pass and 152 in the fixed-port pass.
No strict reduction survived either pass, and no target or nonconstant divisor
sample was zero. The uniform alias and sign checks also found no reduction.
The retained double-negation and square-sign positive controls were detected.

An exact identity in an enumerated family must survive its applicable modular
samples, so a rejection is decisive for that family and sample configuration.
Passing samples would not establish an identity and would require independent
symbolic proof. The search does not cover arbitrary three-or-more-gate
replacements, coordinated changes at several targets, arbitrary new integer
leaves, changes that preserve only zeros, witness reparameterizations, or a
global lower bound. In particular the fixed-port pass uses the four present
ports and 0–4 as leaves, not arbitrary integers precomputed from those ports.

The separate existing `../rational-carrier64-independent/` construction gives
the *same polynomial* in 64 operations using the fixed noninteger rational
leaf `MF / beta`; it does not meet the maintained integer-leaf metric. Its
ordinary and Lean qualification boundaries are recorded in that packet.

Reproduce the read-only run from the DiophantineConsistency directory:

```sh
python3 -I -S -B research/current14-carrier65-local-rewrite-search/search.py > /tmp/carrier65-local-search.json
cmp /tmp/carrier65-local-search.json research/current14-carrier65-local-rewrite-search/result.json
```

The wrapper parses only the four pinned engine function definitions and does
not execute the engine's original graph search. It pins the current complete
JSON graph and its four port files. It performs no Lean run, native proof
replay, or PDF interpretation.

Independent review and a separately implemented enumerator are in
`../../reviews/current14-carrier65-local-rewrite-search-independent/`.
