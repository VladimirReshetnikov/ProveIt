# Restricted sign-aware local search on the 95-gate circuit

This search addresses a limitation of the neighboring node-value-preserving
prefilter. It identifies original intermediate nodes whose **every** direct
consumer is a multiplication of that node by itself. Replacing such a node
by its negative preserves those squared consumers and therefore the final
integer polynomial. In the pinned graph the only eligible nodes are
`Dstar`, `Z`, `f`, `polarA` and `vn`.

For each eligible node, `search.py` searches one- and two-gate ways to
compute its **negative**, using earlier original nodes, inputs and literals
0–4. It tries `+`, `-`, `*`, both subtraction orientations and a square of
the fresh intermediate, then counts nodes reachable from `P12`. It runs both
the independent-port and retained-fixed-port modular passes of the pinned
neighboring search. No size-reducing candidate survived either pass. The
positive control inserts a redundant sign reversal at `Z`; the search finds
ways to remove a gate while preserving the final squared expression.

The first and second passes each inspect 72,767 possible first gates at the
five eligible targets, 1,663 second-operation queries and eight square-root
queries. No sampled target or nonconstant operand is zero. As in the base
search, `t+t` is represented by `t*2` and `t-t` cannot match a nonzero
sample. The fixed coefficients are decoded from hash-pinned files externally;
a modular survivor would require an exact proof.

Run `python3 -I -B search.py` from any directory. It first verifies and
executes the pinned neighboring search (including its payload checks and
positive control), then reports its own result. The recorded output is
[`observations/search.json`](observations/search.json). This source SHA-256
is `4472d0c6f9a7a6402e180978c3bf1d62e74e143177d078ea6ddd3d9d18806377`;
the recorded output SHA-256 is
`f8652ff1e46813ff4c24fc372c037f390a6a9e3cbbb54c7726679afeb59c701e`.

This external finite search is not a Lean theorem, a global size lower bound,
or evidence that other equivalence-preserving changes cannot reduce the
circuit. It does not cover arbitrary downstream contexts, multiple changed
nodes, new variable encodings, or longer intermediate expressions. The
95-gate compact iPRA endpoint and file/PDF binding remain separate work.
