# Independent architecture review

Baseline: `6f0d42d368506bc29c70ace1c992ed88b2651346` of VladimirReshetnikov/ProveIt.
This is a source and theorem-contract review; it does not claim a new full endpoint compilation.

## Exact claim to preserve

The maintained Lean theorem is

```lean
KEndpoint215.blank_halts_iff_zfc_refutation :
  BlankHalts machine215 ↔ BProv ZFCax_s [] Form.fBot
```

The nonhalting/consistency statement is its propositional negation. The maintained
Rocq theorem is `K215F.CorrectDense215.tm215_halts_iff_ZFC_inconsistent`.
The verification README explicitly distinguishes these external proof-assistant
theorems from a proof encoded in PA or in ZFC's own derivation syntax. Neither
endpoint assumes Con(ZFC), and neither proves unconditional nonhalting.

The current endpoint is already a short composition through dense-state
renaming, blank initialization, binary/source simulation, source/program
correspondence, proof enumeration and the ZFC calibration. Compressing the final
four-line composition provides little substantive benefit. The useful target is
the interface between site certification and the generic simulation.

## Semantic coverage: sufficient obligations

Write S for the deterministic source transition function, M for the binary
machine, and R(c,T) for `KSim.Rel`. A halting-equivalence theorem needs:

1. If R(c,T) and S(c)=some c', there is T' with R(c',T') and
   `Reach1 M T T'`.
2. A source configuration with no successor is an actual source halt, not a
   malformed decoder node.
3. An actual source halt related to T implies `Halts M T`.

The forward halting direction inducts on the number of source transitions and
concatenates finite binary runs. The reverse direction inducts on the actual
remaining binary halting time. A positive binary block consumes at least one
unit of that measure. Determinism and partial-run semantics ensure that a
successful binary block cannot continue past a missing transition.

The current `Covered` hypothesis hardcodes successful Boolean `checkEdge`
evaluation. The simulation uses only semantic consequences of that evaluation.
A replacement semantic coverage interface should retain the exact consumed
source word, the length bound, opcode/register constraints, branch condition,
overflow expression, box effect and target zipper. It must reject `.node`.

A precise compatibility-friendly halt contract is

```text
HaltPortSpec M Q :=
  forall n vs, length(vs) >= 10 ->
    exists T, Reach M (conc n vs (start Q)) T and T.q = 230.
```

This contract follows from the old symbolic executor without assuming terminal
rows. The original terminal-row premise `forall b, M 230 b = none` turns it into
`Halts`; it can remain exactly where the existing `sim_halt` and `halts_iff`
interfaces use it. Nonhalting edge contracts must conclude positive `Reach1`
for every gap and every list satisfying the unchanged `Valid` branch predicate.

## Progress is a theorem requirement

The decoder prefix may execute zero physical steps: a one-bit instruction has
an empty preceding prefix. This is sound if its suffix contract is positive,
since `Reach.trans_reach1` yields a positive complete source-edge simulation.
Do not impose positivity on every subfragment; do retain it for every complete
source transition.

Weakening every complete source step to mere `Reach` is unsound. Relate a source
self-loop to an immediately halted binary configuration. Every source step can
be simulated by a zero-step identity run, and there is no source terminal to
violate the halt-preservation premise; nevertheless only the binary machine
halts. A well-founded rank on zero-step source transitions can repair a weak
simulation, but it adds an obligation the existing positive runtime already
discharges directly.

## Incremental route to real savings

First expose semantic coverage and recover every old theorem as a wrapper of
the unchanged Boolean checks. This establishes a conservative seam without
claiming that the existing 6,176 branch computations disappear.

Next compose the maintained exact decoder-prefix theorem with symbolic
execution beginning at its `leafPort`, instead of beginning again at `start Q`.
Retain all existing suffix cases initially. This can eliminate repeated decoder
execution before completing a fully parametric primitive/continuation library.
A later stage groups suffix proofs by the accepted language of full `RolePath`
prefixes. Equal source DAG nodes or equal physical state/read pairs alone do not
identify continuation semantics. In particular, all ancestor-sensitive break,
continue, marker/overflow and spare-block effects remain in the contract.

The intermediate implementation must bind the entry port before universally
quantifying gaps/registers. A port chosen separately from each concrete tape
would not provide a reusable symbolic suffix proof. The maintained
`KDecoderPrefix215.entry_uniform` already supplies the right quantifier order.

## Implemented bridge and a literal example

Three additive Lean modules implement this route:

- `KSimPrefix`: universal prefix and positive suffix contracts, an executor
  beginning at an arbitrary symbolic port, its soundness theorem, the old exact
  branch targets, and semantic coverage from total source shape plus all leaf
  contracts.
- `KDecoderSuffix215`: the maintained `leaf_prefix` theorem is composed with
  checked suffixes at its uniform routed entry. The resulting coverage and
  halting-equivalence theorems remain explicitly conditional on finite source
  shape and `CheckedLeafSuffixes`.
- `KDecoderSuffix215Example`: literal source word `000` denotes decrement/test
  of logical register 8. The decoder follows states 84, 95, 27 in two steps,
  retaining the exact preceding `00` and marker. Both zero and nonzero suffix
  branches are kernel checked from state 27. Existing register-box theorems
  then establish the closed all-natural semantic site contract.

The component builder compiled all three modules, including the literal
example, before its final clean reproduction run. Its portable logs and
receipt own the compilation evidence. The example covers two of 6,176 branch
outcomes; it does not discharge `CheckedLeafSuffixes`. Source shape is a cheap
separate Boolean gate, deliberately explicit in this delivered constructor.

The independent `ksim_contract_audit.json` compares the patched KSim against the
baseline: all 15 preexisting executable definitions and all 22 explicit public
theorem statements are unchanged after removal of comments and whitespace.
Section-inferred parameters are checked separately by the builder's original-API
client. This source audit is not an alternative to kernel checking.

The reproducible `decoder_prefix_census.py` traverses the maintained literal
source nodes, roles and blocks. It recovers 4,751 leaves and 6,176 branch outcomes.
Existing block-certificate prefix clocks sum to 165,876 over leaves and 213,945
when weighted by branch outcomes; the shortest is two steps and the longest 55.
These are physical decoder-prefix witness lengths, not symbolic evaluator
reductions, compile-time measurements, proof-object sizes or a promised speedup.

## Prior work and actual remaining differences

The generic idea of semantic site contracts is already described in
`verification/k215/simplification/proposals/further-simplifications/runtime_contexts/README.md`
and in intake 208. The current phase-nine endpoint does not yet consume such an
interface. A checked implementation is a new integration step, not a new
discovery of decoder/primitive factoring.

One-sided certificate checking likewise predates this delivery. Maintained Lean
already uses semantic source symmetry. The proposal directories contain plain,
normalized, and offset Rocq mirror lemmas. The current production `Source215.v`,
however, still evaluates the offset checker in both directions. Reusing the
offset mirror theorem would be a conservative adoption of existing work; no new
mirror theorem is presented in this delivery. The selected Rocq contribution
instead ports the existing representation-independent 58-step Lean core and
provides a thin adapter to the current numerical DomRho8 interface. Its value is
a shared derivation and removal of arithmetic from the generic propositional
argument; the condensed-detachment derivation itself is inherited.

Independent source inspection confirms that the new Rocq core assumes only an
implication operation, a reflexive relation closed under insertion into either
implication operand, modus ponens and restricted rho8 instances. All are explicit
theorem parameters. No truth constant, arithmetic, decoder, injectivity or
transitivity is added to the generic proof. The numerical adapter discharges
growth using the existing Cantor-code projection inequalities and preserves the
baseline's declared `DomImp` / `rho8_all` interface.

## Historical normalized Rocq lane

The `verification/k215/rocq/normalized-91/README.md` records a successful
44-module normalized-certificate/decode-enumerator build plus recursive coqchk.
Its description must not be mistaken for the current `coq/215` source tree.
The source hash comparison in `normalized91_status_audit.json` shows that
`Source215`, `EnumPerm`, and `L1_SoundPerm` differ, and the two normalized modules
are absent from current `coq/215`; the DomRho8 source matches. Therefore those
historical timing and byte reductions are available evidence for an existing
alternative, not a verification receipt for a patch against the present tree.

## Verification requirements

Keep executable definitions and the exact machine bytes unchanged in the first
interface patch. Check unchanged theorem types, compile all modified generic
modules, and compile explicit original-API clients. The first complete endpoint
adoption must rebuild transitive source descendants, even if a predecessor
object happens to have equal bytes. Phase nine already records a rejected
cache-reuse run caused by missing transitive executable-definition invalidation.

Report component compilation separately from an entire K215 endpoint rebuild;
report compile time separately from source size and proof-object size. The
phase-nine site-time comparison is historical, not a fresh controlled paired
benchmark. No new state-count or machine-minimality claim follows from any of
these proof changes.
