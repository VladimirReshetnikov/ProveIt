# First adaptive13 literal-expression bridge

2026-10-29, circuit_reduction. This is a pre-compilation plan. No factor
extraction, zero-existence equivalence in arithmetic models, or HA equivalence
is assumed or claimed by the proposed leaves.

The accepted `NativeAdaptiveGraph.core` contains the 88 paid gates in the
delivered order, with thirteen coordinates
`J,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma` and four ports
`beta,K,MC,MF_source`. Its current standard-domain equivalence is separate.
The intended first bridge preserves the literal gate schedule and the actual
`CurrentWindowCarry2011.ports` definition, including the complete K and the
single `highPort + beta` shift.

## Proposed new files and interfaces

1. `Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean`, importing
   only `CurrentKernelData2011` and `NaturalExpressionSemiring`.
   It defines the exact `expressionAt : (Fin 4 → ℤ) → Expr (Fin 13)` using
   the accepted aliases and ordered let-gates, `expression` at the actual
   ports, and `naturalExpression` by one `var i + 1` substitution. The
   narrow public interface includes the four exact current-port identities,
   the actual split-natural equation predicate, and its positive-shift
   identity over arbitrary `CommSemiring R`. These are genuine generic
   evaluation equalities; no subtraction in R is used. A small generic
   substitution/split-evaluation lemma is appropriate if required. It must
   not expand the full fixed K or the duplicated split expression.
2. `Lean/DiophantineConsistency/AdaptiveEquationSyntax2011Checks.lean`:
   symbolic arbitrary-semiring shift checks, all thirteen coordinate/port
   positions, the once-shifted fourth port, and a subtraction-sensitive
   check showing the split pair retains a negative integer residual rather
   than truncating it. These do not assert a positive zero exists.
3. `Lean/DiophantineConsistency/NativeAdaptiveExpression2011.lean`, importing
   the narrow new file and the accepted `NativeAdaptiveGraph`.
   Prove the exact polynomial identity
   `(expressionAt p).toPolynomial = NativeAdaptiveGraph.polynomial p`,
   integer evaluation equality with `NativeAdaptiveGraph.value p x`,
   and the standard-natural split-zero equivalence with evaluation of that
   polynomial at the natural cast. Bind the fixed expression to the exact
   current ports without importing the entire `NativeAdaptiveCurrent2011`
   source-restoration/consistency closure. The latter's polynomial is
   definitionally this same `NativeAdaptiveGraph.polynomial` tuple.
4. `Lean/DiophantineConsistency/NativeAdaptiveExpression2011Checks.lean`:
   literal fixed-port binding, symbolic generic-port polynomial/evaluation
   equalities, the single positive shift, and public theorem axiom reports.

The separation matters: the narrow syntax must remain usable alongside
Foundation arithmetic, whereas `NativeAdaptiveGraph` currently imports the
broad Mathlib tactic environment through its external Pell proof closure.
No existing definition ownership or imports are changed. The first packet
does not yet introduce a new HA no-zero sentence; generic sentence compilation
already exists and can follow this exact syntax binding.

An inert source audit should compare the new input aliases and 88 let-gates
against the accepted `NativeAdaptiveGraph.core` segment, rather than treating
the operation count of the fully expanded Expr tree as the DAG count. All
fixed ports remain single constant leaves in that source schedule. The Lean
polynomial equality supplies the mathematical binding; the finite text audit
supplies the exact schedule check, without a new degree/minimality claim.

## Bounded dependency refresh

The exact existing custom closure of the three external imports is **52
modules**, **zero Foundation modules**, with **35 explicit package/toolchain
import boundaries**. Historical provenance comes from the independently
accepted Graph ROOT packet and narrow-current definition packet. Current
source and headers are checked against those records, not inferred from a
matching leaf object.

Six source files differ from these historical providers:
`SignedPellResidue`, `SidonPositions`, `SplitGeometry59`,
`NativePellBootstrap`, `WangTiles942Data`, and `CurrentMaskData2011`.
Propagating these changes through the complete reachable DAG requires
**24 fresh existing prerequisites** and allows **28 unchanged cached modules**.
No reused module imports any of the 24 fresh nodes. The frozen JSON lists all
modules in dependency order, records every current source/header and old
provider, and marks old affected objects as excluded from reuse.
Excluded artifacts are observed separately: any missing or changed historical
object is recorded without promoting it to a current provider. Every selected
reusable object must match its recorded hash. The first read-only audit's
excluded-object hash failure and its source snapshots are retained.

The 35 boundary modules use the existing v4.32.0 package/toolchain providers.
Their exact source, primary objects, available private/server/IR companions,
and package/toolchain identities are pinned. Most primary/private/server
records are inherited from the accepted Graph/positive-zero boundary
inventories. Any boundary not in those inventories is explicitly labelled
as a current-package boundary, with its source/object/trace observations;
this is not a fresh package compilation or a new transitive Mathlib audit.
Exactly five boundary names are absent from those two inventories:
`Mathlib.Algebra.BigOperators.Group.Finset.Basic`,
`Mathlib.Data.Fintype.Sum`, `Mathlib.Data.Nat.Digits.Defs`,
`Mathlib.Order.Interval.Finset.Nat`, and `Mathlib.Tactic.LinearCombination`.
The second read-only audit stopped on an over-specific expected list of two;
the complete actual difference above is pinned, and that failed attempt is
retained. This is a metadata correction, with no package or Lean execution.

The prospective private build is 24 dependency-ordered prerequisite commands
followed by the four new source/check commands. It uses only explicit cached
custom providers plus explicit package/toolchain roots, never stale affected
objects or an unrecorded fallback. Every output is a fresh regular file;
accepted objects remain unchanged. No Foundation, whole native closure,
umbrella, or Lake scheduler build is proposed.

Before each authorized command: check the complete input pins and source
snapshots, read the executed driver and relevant complete sources, retain
both new leaf inputs, enforce a 512 MiB disk reserve, then use Lean v4.32.0
with `-M6000 -j1 -DElab.async=false`. Retain all commands, diagnostics,
timings, source snapshots and outputs, including failures. The preflight
auditor itself runs no Lean and constructs no overlay. Compilation awaits
ROOT's independent plan/refresh review.

## Exact scope boundary

The public internal semantics are equality of natural-expression values in
an arbitrary semiring, hence meaningful in nonstandard arithmetic models.
They do not interpret signed integer subtraction as truncated subtraction.
No theorem in this packet derives A0=A1=0, Fs=Fa=1, Pell indices, powers,
window/machine data, or equivalence to the maintained fourteen-variable
equation. Those remain the subsequent substantive adaptive bootstrap.
