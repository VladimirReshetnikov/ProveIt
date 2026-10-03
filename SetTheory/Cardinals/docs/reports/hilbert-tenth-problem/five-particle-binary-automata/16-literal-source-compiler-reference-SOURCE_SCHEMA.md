# Literal source JSON, reversible-two-counter-v1

The root has schema, controls (ordered unique strings), start, halt, class_cut J, and branches (ordered rows). Each row has unique name, source, target, side -1/+1 (left counter0/right counter1), delta -1/0/+1, and guard.

The finite Boolean guard AST supports:
- {"op":"true"}
- {"op":"eq","counter":0 or 1,"value":k}
- {"op":"gt","counter":0 or 1,"value":k}
- {"op":"and" or "or","args":[guards...]}
- {"op":"not","arg":guard}

All k are nonnegative integers. Classes are 0,...,J,>J. Guards and exact image predicates must be constant on these classes. The parser enforces a sufficient syntactic cut: every guard atom threshold k and its updated-counter image threshold k+delta are at most J. The image predicate is computed by substituting c-delta in the source guard and requiring nonnegative pre-counters. It is never supplied as unchecked separate data.

Source guard truth permits only nonnegative post-counters. Domains at a source and images at a target must be pairwise disjoint. Finite class representatives then suffice to verify this source partial-injection condition. The halt control has no outgoing row. Start need not be predecessor-free unless the exact finite-reflection-cycle result is required; sample-source.json has no incoming start row.

State/control codes in certificates may use their ordered indices. Binary head mode ordering is controls in their supplied order, followed by O_e,I_e for nonzero branches in supplied branch order. For each mode, + then - receives the next gap in 1,...,D.

The bundled sample is a completely accepting one-increment source, not a universal source. The universal source remains the separate effective existence theorem of Morita 1996, with the explicit final-exit deletion normalization in COMPILER_PROOF.md.

## Supported Python API and exact validation

The sole supported construction entry point is `compile_source(data)`, where `data`
is a decoded JSON object. The root must contain exactly the six keys listed above;
each branch and guard node must contain exactly its specified keys. Extra and missing
keys are rejected. Objects must be exact built-in `dict`s, arrays exact built-in
`list`s, and strings exact built-in `str`s. All numeric fields (`class_cut`, `side`,
`delta`, guard `counter` and `value`) must be exact built-in `int`s; Booleans,
floats, numeric strings, and subclasses are rejected. `class_cut` must be nonnegative.
There are no other Boolean-valued source fields; Boolean logic is expressed by the
finite guard AST. Cyclic guard objects are rejected. Empty `and` is true and empty
`or` is false. Empty strings are permitted as names if all references and uniqueness
conditions hold. `start == halt` is permitted and still requires halt to have no exits.

The parser checks all rows, including unreachable rows. Its threshold test is
conservative: even a redundant atom must satisfy the cut. Image pre-counter
nonnegativity is checked in addition to guard substitution. For example, `J=0`
with a `true` increment is valid, while incrementing a counter under `eq 0` requires
`J >= 1`. Compilation uses a finite `(J+2)` by `(J+2)` Boolean table for each
source and image guard; memory and compilation time therefore grow with the
source and cut. Arbitrarily large finite inputs may exceed available resources.

The returned `CompiledSource` (`Compiler` is only a type alias), its `Branch` and
`Gate` records, and all nested source snapshots are immutable through ordinary
attribute/container operations. Direct construction of these record classes raises
`TypeError`; underscore-prefixed machinery and `_reversible_binary_baseline.py`
are private implementation/test code and are not construction interfaces. As with
ordinary Python frozen records, deliberate low-level reflection such as
`object.__setattr__`, class monkey-patching, or memory manipulation is outside this
immutability guarantee. The compiled object retains neither input dictionaries or
lists nor caller-provided functions. `source_data` is a read-only snapshot with
objects represented by mapping proxies and arrays by tuples. Mutating the original
input after `compile_source` returns cannot change the rule.

`C.encode(q, c0, c1, sign='+')` requires a declared string control, two exact
nonnegative integer counters, and sign `'+'` or `'-'`. `C.step(x, inverse=False,
verify=False)`, `gate.apply(x, verify=False)`, and `gate.raw(x)` accept exact built-in
`set` or `frozenset` inputs containing only exact integer positions, including
negative positions. Other containers, floats, Booleans, and subclasses are rejected;
the runtime flags must be exact Booleans. A Python set that already coalesced, for
example, `1` and `True` cannot reveal a discarded element; validation applies to
the elements actually present. Every valid finite position set is allowed, including
empty, dense, noisy, and non-encoded configurations. `step` and `apply` return
`frozenset`s. `Branch.guard(c0,c1)` and `Branch.image_guard(c0,c1)` read the immutable
class tables on exact natural counter arguments. `ledger()` returns a fresh
ordinary dictionary whose mutation cannot alter the rule.

Malformed types raise `TypeError`; malformed structure and source semantics raise
`ValueError`. Runtime verification failures raise `RuntimeError`. None of these
checks uses `assert`, so the same contract applies under `python -O`.
