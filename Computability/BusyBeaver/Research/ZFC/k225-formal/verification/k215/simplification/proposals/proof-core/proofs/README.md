# Checked proof-core simplifications

Base repository: `VladimirReshetnikov/ProveIt`, commit
`aa66d0a33f1f8237a348899eb8095b045a502832`.
This folder contains source proposals and independently recorded local checks.
It does not contain a new Turing-machine transition table, and it does not claim
that the entire ZFC-to-215-state endpoint was rebuilt in this experiment.

## 1. Representation-independent dominated implication

The principal change factors `BusyBeaver/ZFC/DomRho8.lean` into a generic theorem
and an exact adapter for its current public API. The generic theorem is stronger
than the previous statement. Let `I : A -> A -> A`, let `below` be a relation,
and write

```
rho8(a,b,c,u) = I (I (I c u) a) (I (I a c) (I b c)).
```

Assume only:

1. `below a a` for every `a`;
2. `below u x` implies `below u (I x y)`;
3. `below u y` implies `below u (I x y)`;
4. `T (I a b)` and `T a` imply `T b`;
5. `below u a` implies `T (rho8 a b c u)`.

Then every instance `T (rho8 a b c u)` holds, without a restriction on `u`.
The theorem needs no designated truth constant, no bottom element, no
transitivity of `below`, no injective representation, no decoder, no arithmetic,
and no equation identifying an implication with a constant. The temporary
proved seed in the proof is supplied by the already available instance
`rho8 a a a a`. Hence a truth hypothesis is unnecessary even when the carrier
has no globally chosen inhabitant.

The finite condensed-detachment proof was optimized by thirteen new schematic
modus-ponens replacements. Unused-node elimination retains 84 of the old 117
numbered helpers. Only 82 are ancestors of unrestricted rho8 itself; the
remaining two retain the existing public distribution theorem. The sibling
logical-core artifact supplies the exact rewrite plan and deterministic replay.
The proof generator is not part of the trusted base: Lean and Rocq check the
emitted direct terms independently.

The final unrestricted-rho8 proof uses composition, interchange, K, and Peirce
directly. It no longer constructs an inductive derivation language and proves a
general deduction theorem just to discharge two hypotheses. Writing `->` for
`I`, its main chain is:

- composition sends `((c -> u) -> a)` to
  `(a -> c) -> ((c -> u) -> c)`;
- Peirce sends `((c -> u) -> c)` to `c`;
- K sends `c` to `b -> c`.

Lifting the latter two implications under the antecedent `a -> c`, followed by
composition, gives the desired rho8 instance. This last step is a small linear
proof and does not require the general S-based deduction construction.

### Measured source changes

| Source | Bytes | Lines |
|---|---:|---:|
| Pinned original `DomRho8.lean` | 30,114 | 517 |
| New generic `DominatedImplication.lean` | 19,752 | 388 |
| Compatible `DomRho8.lean` adapter | 2,526 | 70 |
| Generic plus adapter, total | 22,278 | 458 |
| Independent Rocq generic proof | 18,519 | 362 |

The production Lean replacement is 7,836 bytes smaller (26.0%) including its
new generic dependency, and has 59 fewer lines (11.4%). The stronger theorem
also removes the coded-zero alias from the logical argument. These counts do
not include audits or optional demonstration clients. They are source-size
measurements, not claims about kernel proof-term size or full endpoint speed.

### Public API and integration

Copy the proposed `formal/BusyBeaver/ZFC/DominatedImplication.lean` into that
module path in the Lean tree. Replace `BusyBeaver/ZFC/DomRho8.lean` with the
adapter, or inspect `DomRho8.patch`. The adapter retains the current `DomImp`
record, `le_l`, `le_r`, `sub`, `wim00`, and all three public theorem types
`composition`, `distribution`, and `rho8_all`. The `truth` field remains for
compatibility. The additional `rho8_all_of_restricted` states the stronger
truth-free result for the current natural-number encoding.

The checked `DomRho8PublicAudit.lean` uses explicitly typed clients of all
three old theorems and of `KCodeDom.cdom_iff_c222`; the current downstream
`KCodeDom.lean` is compiled unchanged. Thus the local calculus interface is
checked, rather than merely asserted to match. The full downstream machine
proof should still be rebuilt before merging into its production endpoint.

`SubtermImplication.lean` is an optional independently checked application.
On ordinary implication trees, restrict the fourth rho8 argument to be a
syntactic subterm of the first. This restricted calculus has exactly the same
provable expressions as unrestricted rho8, using modus ponens alone and no
truth axiom. It is a calculus result; a state allocation for an enumerator of
that formalism has not been supplied by this file.

For Rocq, `rocq/DominatedImplication.v` contains the same generic proof using
only ordinary Coq kernel terms. It imports no project encoding and has no
axioms. Its explicit hypotheses are generalized over the carrier, implication,
relation, and predicate. Instantiating it at the repository's numerical `wim`
requires the existing two operand-growth lemmas and modus-ponens/rho8 fields.
This packet checks the generic Rocq theorem independently; it does not claim a
replacement of the entire current Rocq K215 dependency closure.

### Recorded checks

- Lean 4.32.0: all 28 project modules in the import closure of
  `DomRho8PublicAudit`, `PrintKSim`, and `BusyBeaver.ZFC.SubtermImplication`
  compiled in a new directory with no project object reuse.
- The generic rho8, composition, and distribution theorems print no axioms.
  Both syntactic-subterm client theorems also print no axioms.
- The numerical adapter and current calculus clients print the existing
  `propext` and `Quot.sound` dependencies. No new axiom is introduced.
- Coq 8.18.0: a separate new-directory compile of `DominatedImplication.v`
  succeeded; its three public theorem assumption reports say
  `Closed under the global context`.
- A separate recursive `coqchk DominatedImplication` succeeded, including its
  imported standard kernel environment.

Complete output and source hashes are in `verification/lean-receipt.json` and
`verification/rocq-receipt.json`. Timings are one-run observations, not stable
benchmarks. The sources in `formal` include pinned project dependencies so the
local check is reproducible without fetching a moving branch. Original source
metadata are retained where available under `provenance`.

## 2. Four explicit rho8 axiom families suffice

A separate stronger formalism result removes even the hereditary subterm
relation. In the compressed proof, only four occurrence paths are used. The
following four explicit families, together with modus ponens, derive every
unrestricted rho8 instance over any carrier and implication operation:

| Family | The first argument `a` in `rho8(a,b,c,u)` |
|---|---|
| Empty path | `u` |
| Right | `x -> u` |
| Left-left | `(u -> x) -> y` |
| Left-left-right | `((x -> u) -> y) -> z` |

All displayed letters are arbitrary elements of the carrier, and `b,c` are
arbitrary in each family. There is no inequality or membership test in these
axiom schemas. This finite relation is not assumed to be closed under all
implication contexts. Each use of a domination guard in the proof is replaced
by one of the four exact shape constructors. No minimality claim is made about
the number of schemas.

`formal/BusyBeaver/ZFC/FourShapeImplication.lean` is intentionally separate from
the stable generic core and adapter. Its `all_of_four` theorem and the other
public implication theorems have no axiom dependencies. The independent
`rocq/FourShapeImplication.v` states the four axiom families as hypotheses and
contains the corresponding direct proof terms. A fresh Coq 8.18 compile and
recursive `coqchk FourShapeImplication` both succeeded; rho8, composition and
distribution each report `Closed under the global context`.

The new `KCodeFourShape.lean` client replaces only the rho8 constructor of the
current C222 code calculus. It preserves the existing truth constructor,
generalization, other axiom rows and both bundle side conditions. It proves
`CFour n <-> C222 n` for **every** natural-number code, and consequently
`(not CFour F) <-> (not C222 F)`. These client theorems also print no axioms.
There is no well-formedness restriction and no formula-decoding premise.
The truth-free statement concerns the implication lemma; it does not remove
the current calculus's truth rule or a machine initialization routine.

This new calculus supplies a concrete simpler axiom interface to investigate
when changing the source enumerator. It does not itself produce an enumerator
program, a state allocation, a smaller transition table, or a new full ZFC
endpoint. The current machine theorem is not silently transferred to a new
machine by this calculus equivalence.

The numerical client was checked in a separate fresh **13-module** Lean
closure; its receipt is `verification/four-calculus-lean-receipt.json`.
The finite Rocq proof has its own compile/check receipt,
`verification/four-shape-rocq-receipt.json`. The initial 28-module generic/KSim
receipt and these separate receipts retain their exact validation scopes.
The separate logical-core generation bundle's `specialize_four.py --check`
reproduces the finite Lean source
from the fixed generic source and explicit constructor substitutions, checking
both input and output SHA256. `port_four_shape_rocq.py` deterministically emits
the finite Rocq direct proof terms. Both generators are untrusted.

## 3. Exact KSim adoption of an existing positive-simulation theorem

The repository already proposes the generic theorem in
`verification/k215/simplification/proposals/fm215-compression/formal/PositiveSimulation.lean`.
That theorem is reused here unchanged; this packet does not present it as a
new theorem. The new file is `PositiveSimulationK.lean`, which proves the
run-convention adapters needed to use it in the current K-family runtime.
The current `KSim.halts_iff` proof then becomes one theorem application while
retaining the exact original public type.

The adapter expressly retains the distinction between a literal source halt
instruction and failure to decode an instruction. Its `complete` hypothesis
rules out premature decoder exhaustion, and the existing `KSim.sim_stop`
provides that premise from the existing coverage assumptions. Strictly
positive target progress on every simulated source step is also retained.
There is no weakened coverage premise or new machine-specific assumption.

This is an architectural simplification, **not a total source reduction on
first adoption**. KSim itself drops from 355 to 324 lines and from 16,074 to
14,758 bytes. The already proposed generic lemma has 99 lines and the new
adapter has 63, so counting both into a newly enlarged production closure adds
131 lines overall. The reason to adopt it is to share one deterministic
simulation argument among several compilers and proofs; it is optional if
aggregate source size is the only objective.

`KSim.patch` is against the pinned current source. The before and after public
`#check` and `#print axioms` logs are byte-identical and stored in
`verification/ksim-api-before.log` and `verification/ksim-api-after.log`.
The fresh closure check above compiles the proposed implementation and its
exact typed endpoint audit. No transition table changes.

## Reproduction

With Lean 4.32.0 and a Coq/Rocq installation providing `coqc` and `coqchk`:

```sh
python3 run_checks.py --lean /path/to/lean --build-dir /path/to/new-empty-lean-build
python3 run_rocq_checks.py --coqc /path/to/coqc --coqchk /path/to/coqchk --build-dir /path/to/new-empty-rocq-build
python3 run_checks.py --lean /path/to/lean --build-dir /path/to/new-empty-four-lean-build --roots BusyBeaver.ZFC.KCodeFourShape
python3 run_rocq_checks.py --coqc /path/to/coqc --coqchk /path/to/coqchk --build-dir /path/to/new-empty-four-rocq-build --module FourShapeImplication
```

Each runner refuses a nonempty build directory, copies source into the new
build, checks the indicated closure, and writes a machine-readable receipt.
The Rocq proof can be deterministically regenerated from the checked generic
Lean direct terms with `python3 port_generic_rocq.py`; regeneration is an
untrusted transformation and must be followed by the kernel check.
No compiled `.olean` or `.vo` object is shipped as proof evidence.
