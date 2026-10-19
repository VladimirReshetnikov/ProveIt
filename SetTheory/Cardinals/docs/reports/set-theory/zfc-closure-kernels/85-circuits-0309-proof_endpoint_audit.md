# Endpoint audit and transfer obligations

Audited source snapshot: ProveIt `8e012a51d6e7fdad4d903089536427a813009a4f`.
This note concerns source inspection and ordinary mathematical proofs. It does
not claim a fresh Lean build or a serialized derivation in first-order ZFC.

## Exact meaning of the user's endpoint

The requested conclusion is

\[
\mathrm{ZFC}\vdash
\bigl(\neg\operatorname{Halt}(M,\mathrm{blank})
\leftrightarrow\operatorname{Con}(\mathrm{ZFC})\bigr).
\]

Use one fixed recursively described first-order presentation and define
`Con(ZFC)` as absence of a finite proof of falsity in that presentation. The
repository uses `BProv ZFCax_s [] Form.fBot` for refutation. The finite
binary machine includes its exact blank start, full final write/movement of
the halting transition, and the working-state convention excluding a
separate halting label.

The exact 252 endpoint is a closed external Lean theorem. Its README explicitly
distinguishes that theorem from the open PA-internal proof-code/trace task.
The latest 246 construction has a conventional ZFC proof with reviewed
symbolic certificates, but no newly compiled exact-246 Lean endpoint. These
are different proof statuses. The current user's ZFC target does not require
the stronger PA proof. Conversely, the list of usual Lean axioms by itself
does not establish a general Lean-to-ZFC translation.

## Inspected logical chain

| Declaration | Exact role |
| --- | --- |
| `DirtyProgram254.path_halts_iff_native_refutation` | The structured register interpreter at any root satisfying `C254 T ∧ C254 H ∧ Good W` halts iff the exact native theory refutes falsity. |
| `DirtyProgram254.six_nonformula_path_iff` | Specializes to `T=H=W=0`, leaving `N,A,D,X,Y,L` arbitrary. |
| `EnumSafeStart254.complete_from` | Every enumerator starting state halts if `C254(1)`; no initial formula invariant is required in this completeness direction. |
| `Bisim254.prog254_halts_iff` | Compares the full literal decoder program and the structured path DAG for arbitrary register files. |
| `NativeTheory254.c254_refutation_iff` | Numerical derivability of code 1 iff a native-theory refutation exists. |
| `WFTheory.native_refutation_iff_zf` | The native theory and full ZF including Power Set and Foundation have equivalent refutations. |
| `ChoiceCalibration254.zf_refutation_iff_zfc` | ZF and the literal sealed ZFC theory have equivalent refutations. |
| `ChoiceCalibration254.nonhalting_iff_zfc_consistency` | The existing exact 252 binary machine's closed external Lean endpoint. |

The native theory is the universal closure of the actual container principle,
all finite-formula GIC instances, and raw irreflexivity. It is not GIC for
arbitrary external predicates. Arbitrarily deleting formula cases would
change the calibration obligation.

The standard 246 root is `(N,T,W,A,D,H,X,Y,L)=(3,0,0,0,3,0,0,0,0)`.
The source's padded refutation encodings prove tail universality above any
initial candidate counter; a start at N=3 loses no contradiction. The encoded
logical registers with indices at least 9 are zero. Physical spare blocks
are storage used by the binary implementation and are not additional
logical registers.

## Why the specific calibration can be performed in ZFC

First-order syntax, finite proof trees, valuations into a set domain and
satisfaction for a set structure are definable sets in ZFC. Countable
first-order completeness supplies a nonempty set model from consistency.
The proof does not require a transitive model.

For the native-to-ZF direction, use the actual set-sized quotient and its
internally defined well-founded subdomain. The predicate quantifies over
subsets represented inside the model, not over all external subsets and
not over an externally well-founded membership relation. The needed
Separation, Replacement, Power and Infinity closure proofs use translated
finite formulas and the particular container/GIC resources. One must not
replace these checked constructions by the assertion that an arbitrary
ZF-minus-Foundation model already has all the needed Collection properties.

For the converse, a set model of full ZF provides rank containers and the
required finite-formula Collection instances, giving a native model.
Soundness and completeness turn these model comparisons into refutation
equivalence.

For ZF versus ZFC, take a set model A of ZF and the subset of its domain
defined externally by the model's internal constructibility predicate.
Although A regards its constructible universe as a class, its elements
form a subset of the external set domain. The induced structure satisfies
the actual ZF axioms and its internal `V=L`. Its canonical constructible
well-order gives the required internal selector set through the actual
Separation scheme. Metatheoretic choice of an element from each external
set would not prove this internal Choice axiom. The source explicitly
exhibits an inhabitant, preventing an empty-domain shortcut.

All formula schemes here are syntax-indexed and their relativization
arguments are uniform finite-formula inductions. Formalizing this
particular set construction in ZFC therefore does not need a truth
predicate for the ambient universe, an externally standard model of
arithmetic, or a generic interpretation of all Lean universes in ZFC.
No new proof-assistant run is inferred merely from this source audit.

## What can be changed safely

The provided `compiler_transfer.tex` and `leaf_cfg.py` allow a new decoder
tree to be checked through its complete finite control graph. They treat
break/continue path arithmetic literally; a syntactic reassociation is
accepted only when the resulting successors actually commute with the
site map. Empty paths and implicit trailing zeros are handled by the
selected-leaf quotient. This is independent of the binary simulation
engine.

The provided `safe_start_proof.tex` and `safe_start.py` admit additional
nonzero provable formula codes and safe stack codes. For example, code3
is equality reflexivity and is valid in either formula field. These
certificates discharge a logical premise only. They do not weaken the
full-tape, clean-PC, gap, or spare invariants required by the binary
runtime.

For a contextual state fold, row commutation under a state map is useful
only on a proved domain of reachable state/read pairs. Initial blank
behavior may lie outside that domain. Replacing the start by another
state requires its own literal complete bootstrap. The fact that a new
table omits old states does not prove that the old execution avoided
them.

For a shortened detector, the invariant must cover every intermediate
word encountered on the changed route, including temporary unary zeros,
counter restoration, trailing zeros and overflow. The old source's 18
decrement paths that produce long zero words must be accounted for by
the actual recompiler or a stronger invariant. A larger clean root gap
does not by itself prohibit temporary false delimiter patterns.

The positive-segment theorem is already present in the prior `Beyond 246`
report; the included note attributes it and supplies finite-halting-time
reflection as an alternative proof. It requires positive progress and
complete frame restoration but not unchanged macro durations, decoder
paths or old exit labels.

## Claims to avoid

- Ordinary graph reachability or absence of exact bisimulation is not a
  state lower bound.
- Finite instruction samples, even millions of literal steps, do not
  establish universal unbounded register contracts.
- A complete symbolic instruction proof need not include a finite
  initializer unless that initializer is separately certified.
- A binary proof for 252, 250, 247 or 246 does not automatically bind a new
  changed table with a different start.
- The desired equivalence does not prove `Con(ZFC)` or unconditional
  nonhalting. Under consistency, Gödel's second theorem excludes a ZFC
  proof of nonhalting. Excluding a ZFC proof of the false halting sentence
  requires an appropriate soundness condition, such as Sigma-1 soundness;
  consistency alone is not a general two-sided independence argument.

## Source links

All links below use the audited snapshot:

- [Exact252 README](https://github.com/VladimirReshetnikov/ProveIt/blob/8e012a51d6e7fdad4d903089536427a813009a4f/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/README.md)
- [DirtyProgram254](https://github.com/VladimirReshetnikov/ProveIt/blob/8e012a51d6e7fdad4d903089536427a813009a4f/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DirtyProgram254.lean)
- [EnumSafeStart254](https://github.com/VladimirReshetnikov/ProveIt/blob/8e012a51d6e7fdad4d903089536427a813009a4f/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/EnumSafeStart254.lean)
- [NativeTheory254](https://github.com/VladimirReshetnikov/ProveIt/blob/8e012a51d6e7fdad4d903089536427a813009a4f/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/NativeTheory254.lean)
- [WFTheory](https://github.com/VladimirReshetnikov/ProveIt/blob/8e012a51d6e7fdad4d903089536427a813009a4f/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFTheory.lean)
- [ChoiceCalibration254](https://github.com/VladimirReshetnikov/ProveIt/blob/8e012a51d6e7fdad4d903089536427a813009a4f/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ChoiceCalibration254.lean)
- [RegisterPath](https://github.com/VladimirReshetnikov/ProveIt/blob/8e012a51d6e7fdad4d903089536427a813009a4f/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RegisterPath.lean)
- [Code254](https://github.com/VladimirReshetnikov/ProveIt/blob/8e012a51d6e7fdad4d903089536427a813009a4f/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean)
- [TarskiFalsity](https://github.com/VladimirReshetnikov/ProveIt/blob/8e012a51d6e7fdad4d903089536427a813009a4f/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/TarskiFalsity.lean)
- [Reviewed246 intake](https://github.com/VladimirReshetnikov/ProveIt/blob/8e012a51d6e7fdad4d903089536427a813009a4f/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-162-source-63.md)

