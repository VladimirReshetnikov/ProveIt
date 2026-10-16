# Smaller machines for Con(ZFC)

The goal is a binary, single-tape machine with fewer than 254 nonhalting
states whose blank-tape non-halting is provably in ZFC equivalent to
Con(ZFC). The goal remains open. All new formal work uses Lean.

The [attributed upstream baseline](../../../../lib/jeff-busy-beaver-zfc254/README.proveit.md)
is imported at commit `297ab8df7e5de329605c3875b4934643b371a5e3`.
Mira-Cult designed the machine; Jeff supplies the published verification.
Its exact table has 254 working states, two symbols and terminal label 254.
Our new Lean representation proves finite table facts; the upstream
end-to-end consistency equivalence has not been ported to Lean.

## Intake and theory minimization

[Intake batch 143](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md)
was completed before this research: placement `b07d1a27b`, reconciliation
`83ef1da6b`, catalogue `1ce7ab050`. The three source archives remain
recoverable from arrival `9e5b610259cd42c88e2cf6c862fb876a7c6d6fcd`.

[subset_only.md](subset_only.md) proves, at the mathematical level, that
the membership arm can be removed from source 02's mixed local bound.
A positive singleton-decoder hull covers the root's members without
containing the root. This recovers Separation and Union noncircularly.
The candidate remains an infinite schema, with arbitrary parameters and
matrices; its full deductive ZFC calibration is not yet a Lean theorem.

[Mira's container comparison](mira_containers.md) records the user-supplied
insight and its independent mathematical audit. Mere transitive containment
and power-bounding transitive containment have different strength.
One-sided profile congruence suffices: universally swapping its two variables
recovers the other direction. [rejected_deletions.md](rejected_deletions.md)
gives a `V_{ω₁}` countermodel to deleting transitivity from EFH.

`kernel_metrics.py` compares all candidates in declared common formula
bases and emits actual example-instance RPN/binary encodings. In source 02's
unchanged falsity/implication metric, deleting the membership arm saves four
nodes: point control 69→65, subset control 72→68, and symmetric equality-free
control 83→79. Replacing symmetric congruence by one-sided congruence takes
the last count to 71; in the unary-negation metric it is 58 raw / 56 after
double-negation cancellation. These are formula measures. An example matrix
`Mem(0,1)` is one instance, not the whole schema.

## Lean results

The opt-in umbrella is `BusyBeaver.ZFC`. Its current components are:

| Module under `../../Lean/BusyBeaver/ZFC/` | Proved scope |
|---|---|
| `ProfileCongruence.lean` | One-sided/full profile congruence equivalence; equality erasure and formula invariance for the existing `SetTheory.Form` syntax. |
| `PositiveClosure.lean` | Exact constant fibers, singletons, Power Set, gated decoder root coverage, Separation and Union, under explicit per-relation semantic closure instances. |
| `DeepPositiveClosure.lean` | Actual `SetTheory.Form` wrapper with checked binder renamings, preserving equality-freeness; satisfaction equals the intended definable closure instance. |
| `StateReduction.lean` | A valid transition quotient preserves every finite run, arbitrary/blank halting and exact final score in the existing machine model. |
| `Table254.lean` | Literal baseline table, bounds, halt-edge count and initial action, checked by kernel `decide`. |
| `FormulaRPN.lean` | Three-constructor NAND formula syntax; exact prefix-token parsing in both directions; De Bruijn scope check and a closed semantic contradiction. |

No theorem here supplies a proof-producing theory translator, a complete
refutation checker, an enumerator compiler, a verified binary decoder, or
the final ZFC machine endpoint. `PositiveClosure` deliberately assumes the
specific closure instances used by each lemma, rather than silently assert
all second-order relations form an implemented first-order schema.

The Lean prefix/de Bruijn codec and Python postfix/named-variable bit codec
are distinct encodings. Only the stated Lean token codec has a Lean theorem.
Three token forms still carry natural-number atom payloads. Axiom audits
show no custom axioms or `sorryAx`; only the repository's ordinary Lean
foundational axioms occur. The literal finite table facts have no axioms.

Rebuild the entire small dependency closure **serially from source**:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/check_lean.py
```

This compiles `FirstOrder.Fol`, `BusyBeaver.Core`, the six small modules and the
umbrella into a fresh scratch directory, without shared oleans or Lake's
worker pool. [results/lean-verification.json](results/lean-verification.json)
records the source check and axiom outputs. The pinned Lean toolchain must
be installed. The standalone BusyBeaver Lake package also declares its
FirstOrder path dependency; the ZFC umbrella is opt-in.

The separate [NoQuotient254 result](no_quotient254.md) proves every exact
step-preserving state quotient of this literal machine is injective. Its
13-round finite certificate is checked by Lean kernel `decide`. This is a
narrow obstruction to one reduction method, not a lower bound for other
equivalent machines. It is an expensive opt-in check:
`check_lean.py --include-no-quotient` (about two minutes and several GiB
in the recorded run). It is excluded from the small umbrella.

## Executable experiments and reusable repository ideas

`audit_tm.py` checks the literal table and searches conservative reductions.
The recorded [baseline audit](baseline-254-audit.json) finds all 254 states
graph-reachable and all distinct after step-bisimulation refinement.
A radius-four window abstraction, 64 steps per side and 64,262 ordered
pairs finds no certified single-state merge. The 264,982-step boot prefix
reaches state 96 at head −8 with 149 ones. This finite trace proves no
future invariant; failed reduction searches prove no global lower bound.
The generic exact quotient rule and the literal no-quotient obstruction are
formalized; the Python implementation
and window/macro argument are not formalized.

Useful repository material is recorded with exact source declarations in:

- [repository_ideas_set_theory.md](repository_ideas_set_theory.md): lightweight syntax, data-valued proof trees, proof transport, internal recursion and choice-free certificates.
- [repository_ideas_surreal.md](repository_ideas_surreal.md): exact parser/scope validation already adapted here; arithmetic guards and the limits of surreal round-trip axiom schemes.
- [repository_ideas_diophantine.md](repository_ideas_diophantine.md): stream codes, exact trace certificates, simultaneous witness packing and their true costs.

`stream_encoding.py` tests a 2-adic natural-field stream. For the concrete
NAND example it uses 2,831 fairly framed bits versus 3,080 in the gamma-field
encoding (249 saved). In a natural register the unframed payload is 2,789
bits with the register boundary supplied by the machine model. This is an
encoding experiment, not a state improvement or a verified Lean bit codec.

The [public compiler route](compiler_route.md) reconstructs the published
219-node register DAG offline as a 281-state table using Andrew Wade’s
licensed backend. Replacing its recursive Cantor pair/unpair helpers with
naive 2-adic helpers increases the count to 305. This compiled experiment
shows why the smaller flat stream needs a backend suited to streaming;
the whole-program calibration and compiler simulation remain unproved.
The original single-marker interpreter’s phase interface is recoverable
from the published decoder paths and is the next assembler target.

Run the Python regressions with:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/test_kernel_metrics.py
uv run --no-project python Computability/BusyBeaver/Research/ZFC/test_stream_encoding.py
uv run --no-project python Computability/BusyBeaver/Research/ZFC/audit_tm.py --self-test
```

Regeneration of `kernel_metrics.json` and `stream_encoding.json` is explicit
by running their respective generators. Delivered intake files stay unchanged.

## Next proof and compiler work

1. Extend the now-defined first-order closure schema to a complete theory
   presentation and express every bootstrap matrix; connect all set-existence
   derivations to actual axiom instances.
2. Finish both proof translations, retaining the distinct Foundation/Choice
   consistency bridge and the user's ZFC metatheory.
3. Choose a data-valued proof certificate and prove checker soundness and
   enumeration completeness. Compare runtime encodings through one backend,
   charging initialization and the contradiction target.
4. Compile an actual candidate and transfer its behavior to the literal
   binary table with Lean proofs before announcing any new state bound.
