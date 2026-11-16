# Lean artifacts: exact status and rebuild

The standalone foundational files use Lean **4.32.0** and `Std` only.
They were compiled in the delivery environment. No `sorry` or user-defined
`axiom` declaration is used in these foundational files.

```sh
LEAN_BIN=/path/to/lean-4.32.0/bin/lean ./build.sh
```

With Lean 4.32.0 on `PATH`, `./build.sh` suffices. The script emits `.olean`
files locally; these reproducible binaries are omitted from the archive.
It also builds the application modules if they are present. The script does
not build `RepositoryBridge.lean`, which has the separate dependency described
below.

## Two logically distinct layers

| File | Meaning and verified status |
|---|---|
| `FiniteContracts.lean` | Compiled semantic Lean proofs for bounded-loop invariants, least bounded search, recovery from bounded existence, finite-prefix extensionality, and producer composition. `Nat → Bool` is a host parameter: this file does **not** declare every such function primitive recursive. |
| `ObjectKernel.lean` | Compiled standalone copy of the pinned repository's scoped syntax, intuitionistic natural deduction and ordinary iPRA definition. All original declarations and proofs are retained; only the imports change, plus the notation `ℕ := Nat`. |
| `ObjectBridge.lean` | Compiled object-theory interfaces. A `Contract` contains a fixed `PR n` witness program **and** a `Prf PRAAx` certificate. Existential introduction and quantifier-free induction use the actual embedded deduction system. A record with a proof field is an obligation; it is not a theorem that arbitrary records can be instantiated. |
| `ObjectExamples.lean` | Compiled actual object-iPRA derivations. Defines addition by explicit PR syntax and proves the closed quantified theorem `∀ x, add(x,0)=x` using object quantifier-free induction. Also instantiates a simple output contract. |
| `AxiomAudit.lean` | Compiled `#print axioms` checks for the above main lemmas. Output is in `../verification/lean_axioms.txt`. No audited theorem uses `sorryAx` or `Classical.choice`. Some use the standard Lean metatheoretic principles `propext` and `Quot.sound`, as the upstream kernel does. |
| `RepositoryBridge.lean` | Source-level integration adapter, **not compiled here against the full ProveIt dependency closure**. It applies the exact upstream `pra_iff_native` and `native_iff_pra` interfaces. |
| `AnalyticTargets.lean` | Compiled **definitions and UNPROVED named propositions** for regular rational names, equality/order, finite arithmetic tables, deterministic soft endpoint selection, represented finite-window bounds, rational-domain uniform continuity, extension to represented points, and dyadic-grid integration. It has no theorem assertions for those targets. |
| `SelectionTargets.lean` | Compiled definitions and **UNPROVED targets** for a finite rational residual minimizer, coherent names from an isolation modulus, the residual-zero output, and a deterministic empty-window search under a cardinality bound. The scalar interval version is concrete; the finite-dimensional coordinate extension is documented. |
| `ChartProducerTargets.lean` | Compiled **definitions and UNPROVED named propositions** for the simple-root certificate producer. Defines Gaussian rational pairs and their norm, every natural-number constant and sample precision, coefficient sampling, the finite majorant producer, represented root/inverse hypotheses, and the complex truncated-series kernel. Three closed arithmetic examples are kernel-checked; the producer and contraction targets are not asserted theorems. |

Other application files have their own comments and the archive's validation
report. The table above describes only this foundational component.

### Concrete API for the represented-analysis targets

`AnalyticTargets.lean` is in namespace `IPRAFramework.AnalyticTargets`.
`RealName` is concretely `Nat → Rat`, and `RealSequence` is `Nat → RealName`.
`Regular`, `NameEqual`, `NameLE`, `NameLower`, and `NameUpper` use explicit
dyadic-error comparisons; they are not undefined abstract predicates.

The represented finite-window construction is fully defined:

- `start g i` computes the candidate starts by `n ↦ n+g(n)+1`.
- `windowCount k B = 2^(k+1)*B+1`.
- `endpoint` reads the stage-`k+3` rational observation.
- `firstMin` scans a finite prefix, replacing its stored index only on a
  strict improvement; ties therefore keep the first index.
- `selectedIndex` and `selectedStart` instantiate that algorithm.
- `stabilityMargin k B = 2^(-k)/(2*windowCount k B)`.
- `RepresentedWindowTarget` names the still-unproved theorem that under
  regularity, represented monotonicity, and the range bound, for all window
  indices `u,v` and precisions `p`,

  ```text
  |q(u,p)-q(v,p)| ≤ 2^(-k) - stabilityMargin(k,B) + 2·2^(-p).
  ```

The same module gives concrete finite-gate evaluation and rounding functions,
the `ArithmeticTableErrorTarget` for `L=2B+3`, rational cube-point and grid
encodings, `UniformEvaluator`, `extensionName`, and `integralName`.
`FiniteGridIntegralTarget` names the explicit `3·2^(-k-3)` estimate.
These targets are definitions of type `Prop`; compilation does not prove
them. Object-iPRA completion still requires the fixed PR symbols and
`Prf PRAAx` derivations described below.

### Concrete API for the simple-root chart producer

`ChartProducerTargets.lean` is in namespace `IPRAFramework.ChartProducer`
and imports `SeriesTargets` plus its `Std` dependencies. `Gaussian` is
explicitly a pair of `Rat` values; `gadd`, `gmul`, `gpow`, guarded `ginv`,
and `gnorm` implement complex rational arithmetic and the norm `|re|+|im|`.
The coefficient arrays and majorants are finite nested lists, with zero
defaults outside their bounds.

The executable `constants` and `produce` definitions implement the article's
formulas for `A`, `M1`, `M2`, `Uij`, `U`, `T`, `W`, `h`, `r`, the root/inverse
sample index `p`, and the coefficient sample index `t`. The two small
coefficient enclosures use the minimum of a coarse majorant and the absolute
sample plus the explicit error `rho/16`; all other entries use the coarse
majorants. `NumericCertificate` states the resulting two rational
inequalities and nonvanishing of the sampled inverse.

`NamedChartHypotheses` gives entirely explicit dyadic arithmetic conditions
for coefficient regularity and bounds, root/inverse regularity and bounds,
and the root and inverse identities. Its identity conditions use finite
polynomial residuals and the named budgets `rootBudget` and `inverseBudget`.
`NamedMajorants` expresses the output enclosure with the linear coefficient
sampling error `coefficientBudget * 2^(-s)`. The principal
`NamedProducerTarget` asserts that these hypotheses imply both the numerical
certificate and those output enclosures. It remains an **UNPROVED Prop
definition**.

The complex series extension is also concrete: `GPoly`, `pmul`, `ppow`,
`operatorApply`, `pnorm`, and `FiniteSeriesCertificate` define Gaussian
truncated arrays and their weighted norm. `GaussianNormProductTarget` and
`GaussianContractionTarget` name the complex versions of the rational
series lemmas. Their proof uses the same finite convolution and
difference-of-powers arguments after proving the Gaussian norm inequality.
The module lists the exact completion order. It does not assert a complex
contraction theorem merely by importing the real-rational specification.

Validation is recorded in `../validation/chart_producer_lean.txt`; the empty
log records a successful Lean 4.32.0 compilation. The independent exact
Gaussian-rational implementation in `../code/chart_producer.py` reproduces
72 finite producer checks and writes `../validation/chart_producer_checks.json`.
Those finite checks are implementation evidence only.

## Provenance and license

Pinned repository: <https://github.com/VladimirReshetnikov/ProveIt>

Pinned commit: `42c64ff3a9f56f2a9edc1525e75ece3b720c7f77`.

`ObjectKernel.lean` concatenates these files in order:

1. `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Syntax.lean`
2. `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
3. `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`

It removes the original `import` lines, imports `Std`, and supplies the
natural-number notation originally supplied by Mathlib. No declaration or
proof within the original source blocks is changed. This was checked by exact
string comparison with the pinned files, not inferred from successful
compilation. Git blob hashes and SHA-256 digests are recorded in
`UPSTREAM_SOURCES.json`; the comparison result is recorded in
`../verification/upstream_comparison.txt`.

The upstream source is licensed under MIT-0 (MIT No Attribution License).
Its license is included as `LICENSE-ProveIt.txt`. The new adapter and example
files are original additions prepared for this report.

## Integrating into ProveIt

Use one kernel source at a time. Inside a pinned, working ProveIt checkout:

1. Use the repository's `ConciseIPRA` modules; do not import this archive's
   `ObjectKernel` at the same time, because they define the same names.
2. Change `ObjectBridge.lean`'s first line from `import ObjectKernel` to
   `import ConciseIPRA.PR`.
3. Add the new file directory to the Lake library configuration or copy the
   files to the intended module location and adjust their import names.
4. Compile `ObjectBridge`, `ObjectExamples`, and `RepositoryBridge` with the
   repository's `lean-toolchain` and `lake-manifest.json`.
5. For a proved object sequent `h : Γ ⊢[PRAAx] φ`, apply
   `pra_iff_native.mp h`. This transports **derivability**, not merely truth
   in the standard model.

## Precise remaining formalization work

The human proof of the framework is developed in the article. Its full
object-level compiler is not claimed to be implemented by these examples.
The next modules and their required interfaces are as follows.

### 1. Fixed arithmetic presentations

For each coding operation, provide a `PR k` syntax tree and object derivations
of its defining and domain-preservation laws. Begin with bounded pairing and
sequence access, Boolean connectives and comparison, signed-integer
operations, and rational cross multiplication. Default values on malformed
codes make every numerical operation total; contracts guard the meaningful
cases.

### 2. Bounded formula syntax and Booleanization

Define a scoped bounded formula syntax with primitive Boolean atoms,
`and`, `or`, `imp`, bounded `all`, and bounded `ex`. Its translation to `Fm
PTm` uses explicit bound comparisons. Its characteristic-function compiler
uses fixed PR definitions: Boolean operations at connective nodes, finite
conjunction/disjunction folds at bounded quantifier nodes, and bounded search
for existential witness recovery.

The exact theorem to construct is an instance of `Booleanized n`:

```lean
formula   : Fm PTm n
test      : PR n
equivalent : [] ⊢[PRAAx] Fm.iff formula (accepts test)
```

The paper proves that every fixed bounded formula has such an instance.
The proof is by syntax recursion at the metalevel and quantifier-free fold
induction at the object level. Do not substitute a semantic theorem
`formula_holds ↔ test_evaluates_to_one` for the displayed derivation.

### 3. Loop symbols and object certificates

For fixed PR initial state `s₀`, step `F`, and bound `T`, define the state
symbol by primitive recursion. Booleanize its invariant `I`. With the final
bound kept as an input parameter, use the quantifier-free formula

```text
t ≤ T(x) → testI(t, state(t,x), x) = 1.
```

Produce its base and successor derivations. These fill the already compiled
`InductionCertificate` structure. `InductionCertificate.conclude` then calls
the upstream `PRA.qfInd`. Universal elimination at `T(x)` and Booleanization
give the exit contract.

### 4. Syntax-directed composition

Describe source derivations by finite trees whose leaves are supplied object
derivations and whose constructors are assignment, sequential composition,
Boolean branches, and bounded loops with explicit invariants. The compiler
recurses on this finite tree, using object substitution, cut, disjunction
elimination and the loop certificate above. Its result fills `Contract`.
`Contract.existsOutput` introduces the program's actual PR output term.

### 5. Analytic and geometric applications

Instantiate the arithmetic presentations and transition contracts for each
finite rational algorithm in the paper. Global regularity hypotheses remain
explicit first-order assumptions or are proved separately. Every requested
precision and witness bound must be a fixed PR function, numerical input, or
advertised certificate field. A finite checker does not manufacture a missing
height bound, separation modulus or global exhaustion theorem.

## Uniformity limit

There is no total primitive recursive universal evaluator for all PR program
codes. The diagonal function `n ↦ U(n,n)+1` would refute its universality.
Use fixed-symbol schemas, finite tables, or explicitly clocked simulation.
Lean's ability to define a total evaluator by recursion on syntax does not
prove it primitive recursive uniformly in that syntax.
