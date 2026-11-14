# Distributing the PA196 separation quantifier

This component gives an equivalent numerical axiom emitter with **199 macro
tokens**, compared with PA196's 201, and **3,773 primitive source occurrences**,
compared with 3,812. Its mathematical proof gives primitive recursive
translations between proofs in the original and revised numerical calculi,
preserving every conclusion code. PA verifies these translations by induction
on proof length; it consequently proves equivalence of their refutability and
consistency predicates. This is an ordinary mathematical proof, not a newly
exported Lean theorem.

The mechanism is the common-core derivation of

    U(b, X AND Y) <-> (U(b, X) AND U(b, Y)),

followed by currying. It uses the retained implication basis, h1, h6, modus
ponens, and generalization of closed theorems. It needs neither the old nor
the new separation gate. The original guard `c != a,b` is unchanged. No
general variable-substitution rule is assumed. The detailed numerical
definitions, scope audit, proof, and arithmetization argument are in
`distributed_gate.tex`, intended to be included in the main report.

## Reproduce the arithmetic and the selected word audit

Only Python 3 and its standard library are required. From this directory:

```sh
python3 distributed_gate.py inputs/BusyBeaver --output reproduced_words
python3 verify_selected_word.py --receipt reproduced_selected_audit.json
python3 core_countermodel.py --receipt reproduced_countermodel.json
```

To audit the separately supplied physical candidate without importing its
compiler or runtime checker, also run:

```sh
python3 audit_physical_binding.py path/to/distributed-gate-candidate --receipt reproduced_physical_binding.json
```

`distributed_gate.py` first checks the SHA-256 identities of the upstream
source files, counts the primitive expansion of the literal source DAG,
and reconstructs the complete original 201-token AX word from independent
formula constructors. It compares that word with all 201 literal macro
blocks, including their contiguous source boundaries. It then emits the
twelve distributed-gate words and checks their macro multiset and exact
expanded length. Their only multiset change is one additional copy-D,
one fewer constructor, and two fewer push/zero calls. Their sizes are
26, 27, and 19, giving `26 - 27 - 2*19 = -39`.

`verify_selected_word.py` independently checks the exact word chosen for
the grammar experiment. That word also permutes the six heads to emission
order `[1,6,2,3,4,5]` and exchanges the two antecedents of h6. The common
implication basis proves this head exchange in both directions, so the
same proof-translation theorem applies. The receipt records the new
stack order, whose selection ranks must be used by the command compiler.

## Contents

- `distributed_gate.tex`: mathematical report section, including the
  ordinary PA proof-translation theorem and its precise scope.
- `distributed_gate.py`: pinned source reconstruction and twelve-variant
  generator, with explicit validation checks that remain active under
  `python3 -O`.
- `words/`: all twelve words with original head order, plus their receipt.
- `selected_formula_word.py`: the independently written generator used
  by the grammar search.
- `selected_word.json`: the exact selected 199-token word, with the
  additional head permutation and h6 exchange.
- `verify_selected_word.py` and `selected_word_audit.json`: independent
  mathematical emission audit of that selected word.
- `core_countermodel.tex`, `core_countermodel.py`, and its receipt: a separate
  obstruction to the tempting further rewrite that moves the two vacuity
  factors under the outer quantifier. The exact 16-world model validates
  every retained head, but distinguishes the original and moved gates in
  both directions. This rules out a common-core equivalence proof; it does
  not rule out some new bootstrap for the complete altered theory.
- `audit_physical_binding.py` and `physical_binding_audit.json`: independent
  complete-source, relative-control-flow, and blank-startup audit of the
  separate 198-state candidate. The audit checks the whole delivered root,
  every emitted primitive/control edge, all unchanged exterior code, each
  macro's baseline control pattern, the exact selected word, and the full
  finite tape after 58,154 blank-start steps. It does not rerun the generic
  arbitrary-register runtime certificate.
- `inputs/BusyBeaver/`: minimal pinned source snapshots needed for the
  arithmetic checks and to inspect the retained bootstrap proof templates.
- `inputs/SHA256.json`: hashes of every pinned upstream snapshot.

The twelve base words use the six permutations of the three curried
antecedents, combined with the two equivalent antecedent orders in the
lower separation implication. These are a small explicitly checked
family, not an exhaustive logical optimization search. The selected
word is the base `LRP` gate without the inner exchange and with the
additional head changes described above.

## Provenance and licenses

The numerical calculus and original source are from
`jamesyc/BusyBeaver@407cdc356f6b586635e71ac92be394255f4bfea4`, published
under the MIT license, copyright 2026 James Chang. Its complete notice
is retained at `inputs/BusyBeaver/LICENSE`. The source snapshots are
unchanged. New code and prose in this component may be used under the
same MIT terms, with the original notice preserved where applicable.

The original upstream URLs are:

- https://github.com/jamesyc/BusyBeaver/tree/407cdc356f6b586635e71ac92be394255f4bfea4
- https://github.com/VladimirReshetnikov/ProveIt/tree/f1f076e31995f10460838d1846456f4bb9c8ae80/Computability/BusyBeaver/Research/PA/pa196-vs-u208

The second repository's prior source-search research informed the
comparison and search strategy; no ProveIt source snapshot is needed
by this component's checker.

## Verification boundary

This component proves relative equivalence of the numerical calculi and
checks exact formula emission and source counts. Its additional physical
binding audit checks the complete source/control graph and exact finite
startup for the separately supplied candidate. Universal source-to-table
simulation and routing bounds remain the separate compiler and machine
certificate components' obligations. The baseline's full internal
PA consistency biconditional is also a separate issue: a relative proof
translation does not supply any missing baseline-to-machine theorem.
