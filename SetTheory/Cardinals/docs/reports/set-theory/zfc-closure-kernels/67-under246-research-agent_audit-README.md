# Independent baseline audit and semantic decoder search

This directory records a complementary search on the supplied context246
machine. It does **not** contain a smaller verified machine.

## Baseline audit

The 246-state construction is exactly the prefix250 table with old states
`0,1,3,97` deleted, `60/0` redirected to old state 20, `255/0` redirected to
old state 255, and initial state 95. The first identification uses the mandatory
first one of every block `B(v)=0 1^(v+1)`. The second uses the one written by
state 75 before the pulse returns left. These are universal tape facts rather
than exclusions inferred from a blank execution.

The source proof has three distinct layers: the literal 410,735-step blank
prefix; universal register-macro and full instruction certificates; and the
inherited numerical/native/ZF/ZFC calibration. The exact 246-state endpoint
has an ordinary mathematical proof, not a newly rebuilt proof-assistant
endpoint. The internally well-founded submodel and constructible subdomain
arguments are correctly stated using first-order predicates inside arbitrary
set-coded models. They do not assume externally well-founded Henkin models.

The supplied phase exclusions of four source leaves and two positive
decrement guards were already known for permutation252. Reusing them here
must not be described as a new discovery.

## Search method

`decoder_bdd.py` assigns exact reduced ordered decision diagrams to read-only
episodes. Their outputs are the terminal state and relative head position.
Genuine scanning loops are designated macro boundaries. An initial version
also cut two cyclic decoder components; all 25 choices of one cutpoint from
each five-state component were screened. No equivalence was found, including
neighbor restrictions and backward histories through depth 10.

`decoder_symbolic.py` removes the two artificial cutpoints. It remembers
symbols already read, so inconsistent control-graph cycles are pruned by
their actual tape conditions. All explored episodes terminate before a macro
boundary: 49,506 symbolic subconfigurations, at most 20 initial-symbol facts,
and no genuine looping branch.

`decoder_transducer.py` extends the summaries to finite episodes that write
tape symbols. An output consists of a decision diagram for terminal
state/head, together with a finite map from output positions to Boolean
decision diagrams. Unmentioned cells retain their input symbols. Substitution
models reads after writes; a branch tests the original input symbol at its
coordinate. Canonical Boolean reduction removes writes that leave the tape
unchanged.

`decoder_writing_symbolic.py` combines tape writes with exact cycle
elimination. It has 28 protected macro/scan boundaries and processes 579,923
symbolic subconfigurations, requiring at most 35 initial-symbol facts. It
finds no genuine looping branch and no unconditional state equivalence.

The `*_phase.py` scripts observe the original affine symbolic instruction
engine, preserving its rule meanings. Each observed configuration yields a
cube of **guaranteed** tape symbols. Only the guaranteed constant part of a
run of unknown length is used; an opaque register file exposes at most its
leading zero. Thus a cube describes a superset of the possible tapes, for
every nonnegative gap and every register file admitted by that instruction
guard. Primitive operation states hidden inside register-box calls are
protected from removal.

The final complete-writing phase run covers all 8,385 feasible guards, records
878,250 observed configurations and 642,005 distinct cubes, and finds no
state replacement preserving the complete episode endpoint and output tape.
The separate reversal extension also allows an incoming transition to move
in the opposite direction, compensating by an existing state's episode
starting two cells away. Read its final JSON for the recorded outcome.

These are finite searches in explicit families of replacements. They are
not a lower bound on the number of states, and they do not exclude a change
to the register representation, the control protocol, the logical program,
or several coordinated local episodes.

## Reproduction

Python 3.10+ and its standard library suffice. Set `ZFC246_SOURCE` to the
extracted `zfc-context246` directory, then run:

```sh
python3 -B decoder_writing_symbolic_phase.py
```

The default source location is the sibling research layout
`../sources/context246/zfc-context246`. The scripts refresh their own JSON
records. No baseline files are modified. The preliminary imports print
several smaller-search summaries before the final result.

`transducer_regression.json` records a separate literal-interpreter comparison
of 15,744 fixed-seed finite test episodes. This corroborates the decision-
diagram implementation; the tests are not premises of an unbounded proof.

## Architectural observation

The pairs `(63,48)` and `(4,6)` traverse the same unary block words leftward.
Their difference is the action on the control-side pair of zeros:
`48/0` enters state 7, while `6/0` enters state 9. They implement different
control actions after executing a register operation and after marking its
operand. A redesign that gives these two phases a common program-counter
action might share their traversal states. This requires a new decoder/control
simulation; the observation by itself is not a valid state reduction.
