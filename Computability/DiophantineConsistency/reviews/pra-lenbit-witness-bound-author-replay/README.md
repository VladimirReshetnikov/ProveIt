# Foundation lenbit graph: concrete witness bound

`PRALenbitWitnessBound.lenbit_bound` proves over every IOpen model that
Foundation's exact `lenbitDef` graph implies its exact `bnd` transformation
at the common bound `y+1`. The proof extracts the existing quotient witness
bounded by `y`; `divDef` is open and the negated bounded-divisibility part
requires no new unbounded witnesses. Foundation's `bitDef` uses this graph in
the coded membership check `d ∈ L` of the derivation fixpoint. The separate
`expDef` conjunct, binding after substitution into `bitDef`, full membership,
sequence history and full refutation bound remain unproved.

`candidate_lenbit_bound` proves the mapped result in every candidate-PRA
model, and `candidate_proves_lenbit_bound` is an actual candidate-PRA proof of
its universally closed instance. It does not assume IΣ₁ or Σ₁ collection in
candidate PRA and does not produce a bound certificate for Foundation's full
ZFC refutation sentence ρ.

The author build `/tmp/pra-lenbit-bound-6kgkvw7o` passed both source/check
modules and final authentication on the independently accepted 35-module
provider `/tmp/pra-after-five-induction-independent-p0oew8oa/lib`. The inputs
pin that provider's recorded local source/object graph and the exact inherited
Foundation HFS Basic, Exponential Bit, Exponential Pow2, IOpen Basic and
PeanoMinus Functions source/object pairs. Hashing these selected Foundation
pairs does not authenticate their full transitive source closure; Foundation,
Mathlib and other package dependencies remain inherited. `author/` retains
source snapshots, complete logs and terminal state. The check reports only
`propext`, `Classical.choice`, and `Quot.sound` as Lean axioms.

For independent replay run:

```sh
python Computability/DiophantineConsistency/reviews/pra-lenbit-witness-bound-author-replay/replay.py \
  --parent /tmp/pra-after-five-induction-independent-p0oew8oa/lib \
  --expected Computability/DiophantineConsistency/reviews/pra-lenbit-witness-bound-author-replay/author/state.json
```

The driver authenticates the selected parent graph, Foundation pairs and both
client sources before and after and compares source, object and full-log hashes
against the author. Its state records the actual parent-state hash and commands.

The private replay `/tmp/pra-lenbit-bound-rrwmafbv` also passed both modules
with matching source, object and complete-log hashes; its snapshots, logs and
state are in `private/`. The root independent replay `/tmp/pra-lenbit-bound-9nnf4u_8` also passed both
modules with matching source, object and complete-log hashes; its snapshots,
logs and state are retained in `root/`.
