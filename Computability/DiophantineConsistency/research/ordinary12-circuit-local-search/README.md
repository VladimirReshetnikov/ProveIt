# Restricted local search on the 95-gate free-J circuit

`search.py` looks for a smaller live DAG obtained by replacing **one existing
node while preserving that node's value** in the hash-pinned 95-gate circuit by either one binary operation or
two binary operations with one fresh intermediate. Operands come from the
source inputs, literals 0–4, and nodes occurring earlier in the original
topological order. It tries `+`, `-`, `*`, both subtraction orientations,
and a square of the fresh intermediate; after replacement it counts only
nodes reachable from `P12`. It does not change the circuit or its files.
It does not literally enumerate `t+t` or `t-t`: `t+t` is represented by
`t*2` with the same live count, while `t-t` is zero and every tested target
has a nonzero sample. This equivalence is part of the stated search scope.

The script filters candidates using three deterministic assignments modulo
the checked prime 1,000,000,007. Every integer polynomial identity would
have to survive these evaluations; a surviving modular candidate would still
need an exact symbolic/Lean proof. The program makes two passes: one samples
the four ports independently, and the other fixes them to their actual
residues obtained from the restored, hash-pinned coefficient payloads. The
first pass tests identities uniform in the ports; the second also tests
identities specific to the retained fixed coefficients. In neither pass did
a size-reducing candidate survive. Each pass enumerated 1,027,900 possible
first gates across 95 target positions and 25,745 second-operation queries;
the uniform and fixed passes used 200 and 184 square-root queries respectively.
None of the sampled targets or nonconstant operands was zero, so the logged
division/zero exclusions do not hide a candidate in this run's implemented
class. The file decoding and coefficient residues are externally checked,
not established by this search in Lean.

A positive control replaces `P12 = g98 - 1` by the equivalent two-gate
`(g98 + 1) - 2`; the search finds a 95-live-gate one-gate replacement and
a 95-live-gate two-gate replacement for this deliberately 96-gate circuit.
The control checks that the pruning and live-count machinery can detect a
known local reduction; it is not a proof that the search implementation is
complete beyond the stated class.

Run `python3 -I -B search.py` from any directory. The captured output is
[`observations/search.json`](observations/search.json). Source SHA-256:
`98f54938a6eb1a158ffca98581dd5836300e13a6d07f9340ca52ab8ae55f3949`
and captured output SHA-256:
`900114673aa4ee10229634754abfa5af5a02f292c4d29a9af498eddba2e096af`.
Graph SHA-256:
`2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22`.

This is a finite **external prefilter**, not a Lean theorem or a lower bound
on equation size. It does not search multi-node global rewrites, new
auxiliaries, different factorizations requiring more than two fresh gates,
or substitutions that change an intermediate value but preserve the final
polynomial (for example, a sign change before squaring). It does not search
logically equivalent equations with different solutions or variable encodings.
The 95-gate candidate's compact iPRA endpoint remains open.
