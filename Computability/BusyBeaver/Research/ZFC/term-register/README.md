# Complete register implementation of term certificates

The first complete implementation of the [fixed-pattern certificate protocol](../term-certificates/pattern-matching.md)
compiles to **4,704 working states**, including the parser, all twelve rules,
both freshness gates, candidate enumeration and blank initialization. This is
an experimental cost baseline. The checked 252-state machine remains the best
candidate; this experiment supplies no new consistency or compiler theorem.

The [full binary table](full-search.tm) has 9,408 rows, start state 0 and terminal
4704. Its SHA256 is
`324c23d31a98ca46cc83db970a0b943c76c509800ac732a86a3f17339dba25af`.
The [verification record](../results/term-register-verification.json) includes
all six fresh stages, source identities and compiler data. The
[independent source review](../results/term-register-review.json) covers the
verifier and its correspondence with the maintained certificate protocol.

The emitted program uses Wade's increment, decrement with zero branch,
break, continue and halt operations. `term_register.py` supplies an indexed
node reader; `full_program.py` supplies the complete checker. It checks every
arena node and proof row, including unused records, backward references and
the final empty suffix. Earlier proof conclusions are recovered by rescanning
the proof list. All original logical schemas and the full theory bundle are
retained. The two freshness tests use distinguishing paths, so duplicate node
identifiers cannot turn equal values into unequal ones. The halt condition is
the fixed contradiction term B1(0,0).

Finite words are coded by `nil = 0`, `cons(bit, tail) = 2*tail + bit + 1`.
Incrementing the candidate visits every finite word exactly once. The generated
reader implements division by two using literal register operations. This is
slow on long inputs but requires no input-sized Python data structure or host
verifier in the emitted machine. The fixed templates are compiled from the
trusted source50 specification; candidate data cannot choose a different
theory or halt target.

The constant-space parser omits the frontend's early remaining-length tests.
A complete successful parse consumes at least the corresponding minimum
number of bits and requires an empty suffix, so this changes rejection timing
without changing the accepted complete-word language. That observation is an
ordinary parsing argument; codec equivalence has not been formalized in Lean.

The whole program has 4,551 distinct reachable binary control nodes and 153
framework/selector states. These component closures overlap and must not be
added:

| Component | Reachable control nodes |
| --- | ---: |
| Complete verifier | 4,486 |
| Initial syntax scan | 769 |
| Shared node reader | 235 |
| Proof-row parser | 547 |
| All pattern checks | 3,241 |
| Bundle pattern alone | 2,946 |
| Both gates | 479 |

The node reader is already shared. The pattern checks add 3,006 nodes outside
that shared body. The bundle's 62 circuit instructions expand into 197 pattern
visits and 2,364 repeated path edges, allowing up to 2,462 node-reader calls.
The scheduler and reset add another 65 nodes outside the verifier. Register
reuse could reduce the 56 declared registers, but it would leave the dominant
pattern control cost.

This exposes a poor tradeoff in this implementation: removing 2,076 witness
bits from the small bundle certificate increased the verifier's control.
Witness bits are generated as candidate data during unbounded search; they
are not part of the fixed blank initializer. The next comparison should restore
the [supplied-constructor-ID protocol](../term-certificates/README.md) and check
its 62 instructions with one shared loop. The loop must obtain each instruction
from a **trusted fixed** template stream. Its stream initialization, parser,
calling control and scheduler must all be included in the eventual state count.
No state saving for that redesign is claimed yet.

The fresh portable replay took 163.060 seconds and checked:

* 1,020 selected-prefix node-reader cases and 130 literal bit-pop inputs;
* positive controls for all twelve rules and rejection of those same words at
  the fixed contradiction target;
* 261 template assignments, including zero normalization and both failed gates;
* 1,001 literal versus contracted helper comparisons over every final register,
  plus 63 complete parser comparisons;
* all 8,191 words of length at most 12 for structural parsing, and eleven
  malformed controls including unused records and trailing data;
* a separately generated truth-target scheduler, which finds its first accepted
  word exactly at candidate 257;
* the complete compiled table and one million literal blank-tape steps. The
  latter reaches the full main entry at step 39,763 and does not halt within
  that finite prefix; it supplies no unbounded behavior claim.

Large register tests accelerate only explicitly listed arithmetic helper loops.
Parsing, matching, gates and scheduling still execute the generated control.
The literal helper comparisons check every register, including dirty scratch.
A fuel exhaustion is an error, never a rejected certificate. All primitive
helper code remains charged in the compiled table.

Reproduce from the repository root with Python and existing repository data:

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_term_register.py \
  --output /outside/term-register-replay
```

The runner recovers source50 offline through the maintained frontend runner,
copies the seven program/test/compiler scripts into scratch and executes all
six stages. It generates the named table and state map as well as the canonical
table; the former two reproducible artifacts are omitted from this checkout.
`--prepare-only` checks source discovery and copies files without running the
suites. The fresh pre-placement replay used the identical published bytes;
their placement identities are recorded in the verification JSON.

The public Wade backend is recovered unchanged at upstream commit
`297ab8df7e5de329605c3875b4934643b371a5e3`. Mira-Cult's calculus, Jeff Ketchersid
and contributors' verification, and Andrew James Wade's MIT-0 compiler retain
their attribution through the [imported baseline](../../../../../lib/jeff-busy-beaver-zfc254/README.proveit.md).
The source50 specification has SHA256
`fbce2fd79f909cce5b6d0ca52e2c7ead86ce052285294cb7c9dffa657a217adc`;
its original arrival was `85633fd2f57b5dca16f87667699134d1b500ebc0`.

The compiler explicitly selects the complete search root after clearing helper
test names. One missing source transition is completed by writing zero, moving
right and entering the unique terminal. This preserves halting under the
partial-table convention, but changes that terminal step's tape and head.
Full correctness of this new compiled program remains separate from its finite
tests and measured state count.
