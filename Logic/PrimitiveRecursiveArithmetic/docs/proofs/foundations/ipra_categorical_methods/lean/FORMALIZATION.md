# Formalization plan, pinned setup, and proof status

## Status of this delivery

**All three delivered Lean source files are uncompiled.** No Lean executable
was available in the preparation environment. No `.olean` output, successful
Lean build, or theorem-dependency audit is claimed. The mathematical proofs
are in the paper; the Python checks exercise exact finite examples.

`ObjectCategory.lean` contains proof expressions whose stated conclusions
are the repository's actual embedded derivability judgement `Prf PRAAx`.
The two `*Targets.lean` files define host-level data and desired propositions.
A declaration `def Target : Prop := ...` asserts no proof of `Target`.
Compiling such a definition would establish only that its statement is
well formed. This distinction remains necessary even after a future build.

## 1. Verified source and dependency pins

| Component | Pin |
|---|---|
| Repository | `https://github.com/VladimirReshetnikov/ProveIt` |
| ProveIt commit | `bb86091690bc4f920f046a37cfc87719299b4019` |
| `lean-toolchain` | `leanprover/lean4:v4.32.0` |
| Root `lakefile.toml` Mathlib requirement | `leanprover-community/mathlib`, revision `v4.32.0` |
| Root `lake-manifest.json` resolved Mathlib revision | `81a5d257c8e410db227a6665ed08f64fea08e997` |
| ConciseIPRA source directory | `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean` |
| Numerical syntax and axioms | `ConciseIPRA/PR.lean` |
| First-order syntax | `ConciseIPRA/Syntax.lean` |
| Intuitionistic deduction | `ConciseIPRA/Deduction.lean` |
| Native translation endpoint | `ConciseIPRA/NativeBiInterpretation.lean` |

These pins were read from the stated repository snapshot. They are build
targets, not versions with which the new files have already been tested.
Use the committed manifest rather than updating dependencies to their
current default branches.

## 2. Reproducible setup and first compilation attempt

The following commands are instructions for a machine with Git, Elan/Lake,
and network access to the pinned dependencies. They have **not** been run as
a Lean build for this delivery. Replace the one packet path with the absolute
path to the extracted archive.

```sh
git clone https://github.com/VladimirReshetnikov/ProveIt.git ProveIt-ipra-categorical
cd ProveIt-ipra-categorical
git checkout --detach bb86091690bc4f920f046a37cfc87719299b4019
elan toolchain install leanprover/lean4:v4.32.0
lake env lean --version
lake exe cache get
git -C .lake/packages/mathlib rev-parse HEAD
lake build ConciseIPRA.PR
```

The Mathlib hash printed by the penultimate command should be the resolved
revision above. `lake exe cache get` obtains dependency build artifacts; it
does not verify this packet. If the dependency setup fails, resolve that
failure before interpreting any subsequent import error. Do not silently
replace the pins with a different toolchain or Mathlib version.

Copy the three new files into a separate directory in this checkout. They
do not need changes to the repository's Lake configuration for direct
`lake env lean` checking:

```sh
packet_dir=/absolute/path/to/ipra_categorical_methods
mkdir -p IPRACategoricalPacket
cp "$packet_dir/lean/ObjectCategory.lean" IPRACategoricalPacket/
cp "$packet_dir/lean/FiniteCategoryTargets.lean" IPRACategoricalPacket/
cp "$packet_dir/lean/MacaulayTargets.lean" IPRACategoricalPacket/
lake env lean IPRACategoricalPacket/FiniteCategoryTargets.lean
lake env lean IPRACategoricalPacket/ObjectCategory.lean
lake env lean IPRACategoricalPacket/MacaulayTargets.lean
```

These are the intended checking commands, not a promise that the uncompiled
files will elaborate without adjustment. Resolve notation, dependent tuple,
and Mathlib API differences by proving the missing facts or correcting the
implementation. Do not turn an unfinished target into an axiom, insert
`sorry`, or infer the target from its definition. A host specification may
require a `noncomputable` annotation for a Mathlib convenience; that would
not establish primitive recursiveness and cannot replace the numerical
implementation described below.

`ObjectCategory.lean` ends with `#print axioms` commands for three selected
declarations. Only an actual successful run produces an audit. Extend that
audit to all newly proved declarations and record the complete output.
Absence of `sorryAx` or custom axioms is necessary; the theorem's conclusion
must also be inspected to distinguish an object proof from a host theorem.

After the object derivations are complete, the optional native-presentation
stage can build its dependency:

```sh
lake build ConciseIPRA.NativeBiInterpretation
```

The inspected theorem `LeanProofs.ConciseIPRA.pra_iff_native` has the form

```lean
(Prf PRAAx Γ φ) ↔ NPrf (Γ.map NFm.ofPRA) (NFm.ofPRA φ)
```

Use it only on an already obtained arithmetic derivation. It changes the
presentation of the proof, not its assumptions or mathematical strength.

## 3. What each file actually contains

| File | Contents | What remains |
|---|---|---|
| `ObjectCategory.lean` | `args₂`, `bin`; proof expressions for `bin_congr`, `inverse_unique`, `inverse_unique_imp`, `yoneda_covariant_component`, `yoneda_component`, and `contract_cut` | Compile and audit; derive their local categorical premises from concrete arithmetic validity conditions; add the setoid-relation variants |
| `FiniteCategoryTargets.lean` | Concrete list-backed raw categories, functors, diagrams, cones, cocones, presheaves, and representable transformations; exact limit, colimit, and Yoneda target propositions | Boolean validators, actual producers and mediators, their host correctness proofs, numerical PR reification, and embedded object proofs |
| `MacaulayTargets.lean` | Monomial enumeration, coefficient arrays, Macaulay matrix, closure specification, solver specification, action identities, evaluation-vector and denominator-grid targets, complete-list specification | The bounded solver and its proof, labeled certificate synthesis, grid program and correctness, explicit numerical polynomial implementation, and embedded object proofs |
| `CategoryBlueprint.md` | Contract and presented-setoid interfaces; detailed categorical proof strategies | Implementation and proofs; the semantic function fields are not PR certificates |
| `lean-toolchain` | The intended Lean version | Installation and a real build |

The finite-category predicates are deliberately separated. For example,
`IsFunctor c d f` does not itself include `IsCategory c` and `IsCategory d`;
`IsNatural c d f g eta` does not itself include both functor-validity
assertions. Complete theorems must supply these surrounding guards.
`FiniteLimitProducerSpec` and `FiniteColimitProducerSpec` already require
`IsDiagram`; `YonedaDeterminationSpec` requires `IsPresheaf`.

Two representation details need explicit bridge lemmas:

* The Python reference uses `-1` for off-domain composition; the Lean
  numerical lookup defaults to `0` and only constrains composition on
  composable arrows. Canonicalize the off-domain entries when comparing
  representations. All categorical laws concern guarded inputs.
* The paper's coefficient space lists total-degree-at-most-`D` monomials.
  `MacaulayTargets.lean` uses the full exponent box with `(D+1)^r` rows.
  Under `d+1 ≤ D`, the additional rows are zero on the relevant columns
  and right-hand sides. Prove equivalence of these two finite systems.

## 4. The required object-theory endpoint

In namespace `LeanProofs.ConciseIPRA`, the target is

```lean
Prf PRAAx Γ φ
```

where `φ : Fm PTm n` and `Γ : List (Fm PTm n)`. `PR k` represents a
specified primitive recursive definition, `PTm n` its first-order terms,
and `PRAAx.ind` requires `φ.QF` for its induction formula. The derived
interface `PRA.qfInd` takes an object proof of the base and an object proof
of the successor step in the correctly shifted context.

The empty context does not imply that a formula has no free variables.
`inverse_unique_imp` is assumption-free with its `n` variables still
schematic. If a closed sentence is desired, add the appropriate `Prf.allI`
applications and respect their freshness conditions.

A host theorem about `Nat`, `Rat`, matrices, or `CategoryTheory.Category`
does not automatically construct `Prf PRAAx Γ φ`. Likewise, the semantic
evaluator of the inductive type `PR` need not be PR uniformly on numerical
codes. Fix the operations used by each theorem or use an explicitly bounded
interpreter. Do not install a universal evaluation or reflection principle.

## 5. Ordered implementation milestones

### M1. Numerical coding and local arithmetic

Implement the paper's numerical list coding, totalized lookup/update,
length, concatenation, tagged pairs, powers, finite products/sums,
first-success scans, rank/select in retained lists, finite unions,
integer signs, rational normalization, and polynomial coefficient tables.
For each, provide `PR` syntax and object derivations of its local equations.
Maintain validity guards for malformed codes and zero denominators.

All tables are finite data. Their uniform evaluation is distinct from
evaluating arbitrary PR program definitions. Matrix dimensions, exponent
tuple counts, and retained-list lengths may be input parameters.

### M2. Booleanization and loop derivations

For every bounded validation predicate, implement a Boolean characteristic
function and prove equivalence in `Prf PRAAx`. Use prefix conjunction and
first-success registers as in paper Section 2. This permits extraction of
a particular category law or coefficient equation from a successful test.

The guarded-loop rule uses the Booleanization of

```text
t ≤ N → I(x,N,t,S(x,t)).
```

Keep the context independent of local variables `t,z`. An unbounded input
contract may remain in that fixed context. Do not include it in the QF
induction formula. The input point, cone, or candidate solution remains a
free parameter until the finite invariant has been proved.

### M3. Short object-calculus categorical proofs

Compile `ObjectCategory.lean` and discharge its local hypotheses using
M2. Add split-monic cancellation, terminal-object uniqueness, naturality
composition, and unit/counit calculations with the same equality rules.
For a hom setoid, use object formulas for its equality and prove relation
symmetry, transitivity, and congruence; arithmetic Leibniz substitution
alone is insufficient.

The delivered Yoneda component lemma is only the determining calculation.
Implement the reconstructed transformation, prove typing and naturality,
and prove both inverse equations. In the finite case enumerate the
transformation tables. In an infinite fixed presentation retain the result
as a scheme over the supplied PR action and component family.

### M4. Uniform finite constructors

| Construction | Producer and resource | Essential invariant or final argument |
|---|---|---|
| FinSet exponentials | Base-`m` code `<m^n`; bounded digit sums | Prefix digit bound and reconstruction; handle `n=0`, `m=0`, and `0^0=1` before division |
| Functor categories | Enumerate bounded object/arrow maps and component tables | Retained candidates are exactly those satisfying typed functor/naturality tests; componentwise composition |
| Finite limits | Filter at most `∏ᵢ dᵢ` mixed-radix tuples | Exact retained-prefix membership; rank/select inverse; mediator sends a cone point to the rank of its coordinate tuple |
| Finite colimits | Tagged union of size `N=∑ᵢ dᵢ`; `N` Warshall rounds | Paths with internal vertices below the round; simple paths have length `<N`, temporary concatenations length at most `2N`; bounded loop deletion |
| Finite Kan extensions | Left triples at most `qM`; right tuples at most `M^q` | Generator preservation, explicit unit/counit naturality, mediator well-definedness, and inverse correspondence formulas |
| Finite-query contracts | Forward maps and backward finite unions | Membership in flattened query union; object implication cuts; extensional equality of query sets |

For the Kan bounds, `q=|Ob C|·|Mor D|` and
`M=max(1,max_c |F(c)|)`. The constructions quantify over finite input data;
they do not assert limits or Kan extensions for arbitrary infinite data.

### M5. Macaulay certificate synthesis and rational enumeration

Implement the bounded Gaussian solver rather than treating
`ClosureAccepted` as an algorithm. Keep the row identity
`[R | w] = U [A | v]`, the reduced pivot pattern, and either an inverse
operation matrix or a finite inverse-operation log. With `n` column scans
and at most `m` pivots, return either a solution or a separating row.

Retain `(generator_index, exponent_tuple)` labels on every generator-multiple
column. The solved coefficients must construct actual ideal-membership
polynomials, not merely a span-membership claim. Prove each action identity
coefficientwise, including the constant generator `1`.

Prove `EvaluationTarget` by finite sums and polynomial evaluation. For
`DenominatorGridTarget`, scale the nonzero rational evaluation vector to
a primitive integer vector, use bounded extended Euclid for the divisibility
step, and use a first maximum coordinate for the absolute column-sum bound.
Then implement the grid of `∏ₖ(2Rₖ+1)` points and exact filtering. Prove
soundness, completeness for an arbitrary coded rational point, and no
duplicates. These are the ingredients of `CompleteList`.

No matrix-commutation theorem is required. The finite-span proof uses a
fixed variable order, preserving the explicit ideal identity after each
matrix multiplication. No loop increasing degree caps without a supplied
termination bound belongs to this theorem.

### M6. Gluing, modular compatibility, and coherent towers

Finite sheaf gluing uses the least covering patch for each point; the
prefix invariant states agreement with every applicable supplied section.
The invariant has at most `n k` entries. Its hypotheses include exact
overlap agreement and cover validation.

CRT uses bounded extended Euclid and the equation `u a + v b = gcd(a,b)`.
All signed divisions have explicit divisibility/nonzero guards.

For the tower theorem retain the supplied initial value as a parameter.
Implement the least next-stage lift below `b(n+1)` and induct on current
state validity. Adjacent coherence follows from the selector's local
contract. The unbounded covering/surjectivity assumptions remain outside
the induction formula.

For a supplied finite groupoid cover, retain pairwise inequivalence and
coverage of the scanned prefix. Instantiate the global covering assumption
only after fixing an arbitrary object. The least retained representative
then gives the explicit skeleton equivalence.

The binary-tree and two-component obstructions are metatheoretic
computability arguments. Formalizing their metatheory is a separate task;
they are not additional object-theory axioms. Bounded machine simulation
and finite-level witnesses can be implemented inside the arithmetic.

### M7. Native translation and exported certificates

Use `pra_iff_native` only after M1–M6 have delivered the intended ordinary
iPRA derivation. If an executable proof checker is also desired, separately
encode the `Prf` derivation tree numerically, implement its checker, and
prove the encoding/checking lemmas. The inductive proposition `Prf` is
not itself a byte-level executable checker, and no such checker is supplied
by this packet.

## 6. Completion criteria

A result may be labeled **object checked** only after a successful pinned
build of a declaration whose conclusion constructs the intended
`Prf PRAAx` derivation, with its hypotheses listed accurately. A proved host
specification may instead be labeled **host checked**. A defined but unproved
proposition remains a **target**. An exact Python run is **finite executable
evidence**. The current delivery has human proofs, uncompiled object proof
expressions, unproved host targets, and finite executable evidence; it does
not have newly kernel-checked Lean results.
