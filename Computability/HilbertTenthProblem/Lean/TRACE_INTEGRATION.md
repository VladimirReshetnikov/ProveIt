# Diophantine traces, MRDP integration, and universal quartics

The current forward MRDP proof is
[`Common/MRDPCore.lean`](Diophantine/Common/MRDPCore.lean), a byte-identical
copy of the standalone single-file MRDP extraction (not included here). It uses a direct
Chinese-remainder certificate and beta-coded recursion traces, and does not
depend on the cipher proofs of `PAListCoding`. `Diophantine.mrdp` forwards to this
core theorem; the article-facing `rePred_dioph` and scalar primitive-recursion
interfaces adapt the core results to their existing contracts. The
[MRDP guide](MRDP.md) documents this route and its checks.

*Merged into ProveIt:* the vendored twelve-module extraction described below
was replaced by ProveIt's own `PAListCoding` library
(`Logic/PeanoArithmetic/ListCoding/Lean/`), from which it was extracted; the
imports `PAListCoding.CipherOnes`, `CipherRelations` and `IterationDioph`
resolve there. The exact-iteration block that the extraction had cut out of
`TetrationDiophantine.lean` is now the upstream module `PAListCoding.ExactTrace`,
which `IterationDioph` imports, so Foundation stays out of this library's
imports. The provenance record below is kept as history.

The twelve-module `PAListCoding` library and the general trace wrapper remain
part of the project. This guide records their provenance, retained interfaces,
and relationship to the article representation theorems. They are independent
library results rather than prerequisites of the new forward MRDP proof.

**Historical validation, 2026-09-14.** The twelve-module PAListCoding
extraction, unconditional trace wrapper, primitive-recursive and recursively
enumerable bridges, and universal-quartic layer have passed focused builds.
One consolidated `lake build` passed with 3150 jobs. All thirty declarations
in the transitive axiom audit report exactly
`[propext, Classical.choice, Quot.sound]`. The detailed receipt and remaining
article obligations are recorded in [STATUS.md](STATUS.md).

That receipt describes the original integration, before the shortened proof
was transplanted. It does not validate later source changes. New build and
audit receipts belong in [STATUS.md](STATUS.md), which also records the
individual article obligations.

## Source and compatibility

- Repository: <https://github.com/VladimirReshetnikov/ProveIt>.
- Inspected revision: `a9e9c597c2a355702dfe775766ba2c0601653840`.
- Local source root:
  `C:/ProveIt/Logic/PeanoArithmetic/ListCoding/Lean/PAListCoding`.
- [Source at the inspected revision](https://github.com/VladimirReshetnikov/ProveIt/tree/a9e9c597c2a355702dfe775766ba2c0601653840/Logic/PeanoArithmetic/ListCoding/Lean/PAListCoding).
  The source directory had no uncommitted changes when inspected.
- ProveIt's root `LICENSE` states **MIT No Attribution**, copyright 2026
  ProveIt Contributors. The extracted component preserves a byte-identical
  license copy, the source comments, and a record of every adaptation.
- The cipher files explicitly describe their relation to Dominique
  Larchey-Wendling's Rocq development. In particular,
  `C:/ProveIt/lib/Coq-Library-Undecidability/theories/H10/Matija/cipher.v`
  carries an **MPL-2.0** notice. The component preserves these mathematical
  provenance references and copies Lean sources, not the Rocq library.
- ProveIt, its nested PAListCoding package, and this project use Lean
  `v4.32.0`. Their manifests agree on Mathlib revision
  `81a5d257c8e410db227a6665ed08f64fea08e997`. All nine package revisions in
  the nested PAListCoding and Diophantine manifests also agree.

The component needs only the existing Mathlib dependency. `C:/ProveIt` is a
source-provenance location, not a build dependency. See the vendored
[PROVENANCE.md](vendor/pa-list-coding/PROVENANCE.md) and
[SOURCE_SHA256.json](vendor/pa-list-coding/SOURCE_SHA256.json) for the extraction
record and original/copied hashes. The referenced
`lib/Coq-Library-Undecidability` directory is a tracked source tree at this
revision; it is distinct from the `-current` Git submodule.

## Minimal source closure

The sources are under `Lean/vendor/pa-list-coding/PAListCoding/`, retaining
the upstream module and namespace names. `lakefile.toml` registers the
`PAListCoding` library with source directory `vendor/pa-list-coding`.
The following twelve modules form its proof closure. A separate
`PAListCoding.lean` umbrella imports all twelve; the project-owned assembly
wrapper is additional.

| Module | Upstream lines | Treatment |
|---|---:|---|
| `BinaryDioph` | 433 | Byte-identical copy |
| `BoundedDioph` | 370 | Byte-identical copy |
| `PolynomialCipher` | 231 | Byte-identical copy |
| `SparseCipher` | 1,116 | Byte-identical copy |
| `CipherCircuit` | 358 | Byte-identical copy |
| `BoundedCipher` | 329 | Byte-identical copy |
| `CircuitDioph` | 288 | Byte-identical copy |
| `BoundedCipherDioph` | 222 | Byte-identical copy |
| `CipherOnes` | 1,476 | Byte-identical copy |
| `CipherRelations` | 1,009 | Byte-identical copy |
| `IterationDioph` | 177 | Second import replaced by `PAListCoding.ExactTrace` |
| `ExactTrace` | 99 extracted lines | Extracted `TetrationDiophantine.lean:48–146` |

The eleven existing files total **6,009 lines / 242,710 bytes**. The extraction
adds the generic `ExactIter`, `BetaTrace`, and their equivalence proofs, plus
an import of `PAListCoding.BoundedDioph`, `namespace PAListCoding`, and the
matching namespace terminator. No tetration definitions or exponentiation
wrappers are needed for this extraction. Its provenance comment records the
source line boundaries and revision.

The dependency graph after that split is:

```text
Mathlib -> BinaryDioph, BoundedDioph, PolynomialCipher, SparseCipher
PolynomialCipher + SparseCipher -> CipherCircuit
CipherCircuit -> CircuitDioph
BoundedDioph + CipherCircuit -> BoundedCipher
BoundedCipher + CircuitDioph -> BoundedCipherDioph
BinaryDioph + SparseCipher -> CipherOnes
BinaryDioph + BoundedCipher + CircuitDioph -> CipherRelations
BoundedDioph -> ExactTrace
BoundedCipherDioph + ExactTrace -> IterationDioph
```

Importing the upstream files unchanged would instead pull **18 PAListCoding
files plus 99 Foundation files: 37,804 lines / 1,594,921 bytes**. The avoidable
route is `IterationDioph -> TetrationDiophantine -> ExponentiationDiophantine
-> NumberTheory -> Aggregates -> Standard -> Predicates -> Basic
-> Foundation.FirstOrder.Arithmetic.HFS`.

A ProveIt package dependency would also need its Foundation Git submodule
(`32e1a0956a8622fad067328ca1959729a7634428` at the inspected revision).
PAListCoding's nested package reaches it through a relative source directory;
copying only that nested package would break the path. Foundation's own
package advertises Lean/Mathlib `v4.31.0`, although ProveIt registers its source
under the root `v4.32.0` environment. The smaller extraction avoids these
unnecessary package and toolchain complications.

## Unconditional trace assembly

[DiophantineTrace.lean](Diophantine/Common/DiophantineTrace.lean) implements
`Diophantine.boundedForall_dioph`, `exactIter_dioph`, and
`existsExactIter_dioph`. Callers supply the Diophantine bound or transition
relation and endpoint functions; they do not supply unproved cipher closures.

The wrapper constructs `CipherRelations.OnesSubstitutionClosed` using
`CipherOnes.onesCodes_dioph` (upstream line 1465), then discharges all five
contracts with `CipherRelations.code_closed_of_ones` (975),
`constCode_fixed_closed_of_ones` (982), `constCode_closed_of_ones` (989),
`indexCode_closed_of_ones` (995), and `mulRel_closed_of_ones` (1002).
It applies `BoundedCipherDioph.boundedForall_dioph` (203) and
`IterationDioph.exactIter_dioph` (135), and quantifies the iteration length
with `Dioph.ex_dioph` for reachability. The assembly follows the upstream
pattern in `HyperoperationDiophantine.lean:230–293` without importing that
module or its other dependencies.

`ExactIter R 0 x y` is `x = y`; its successor clause appends one transition.
The interfaces use scalar natural-number states and parameter types
`α : Type`. The twelve vendor modules and this wrapper have passed focused
compilation; the broader validation boundary is recorded below.

## Current primitive-recursion and recursively enumerable interfaces

[PrimitiveRecursiveDioph.lean](Diophantine/Common/PrimitiveRecursiveDioph.lean)
retains `Diophantine.natPrimrec_dioph_comp` and `natPrimrec_dioph` as
compatibility adapters to `MRDP.primrec_diophFn`. Mathlib's conversion from
scalar `Nat.Primrec` to arity-indexed `Nat.Primrec'` connects the interfaces.
The first theorem still preserves arbitrary Diophantine input substitutions.

The core represents a finite recursion trace by two naturals `a, b`, reading
entry `i` as `a % ((i + 1) * b + 1)`. Mathlib's beta-coding theorem supplies
the trace, and `MRDP.boundedForall_dioph` makes its transition conditions
Diophantine. This replaces the former scalar induction that paired the fixed
parameter, counter, and current value into a state and applied `exactIter_dioph`.
The pairing and exact-iteration APIs remain independently available.

[RecursivelyEnumerableDioph.lean](Diophantine/Common/RecursivelyEnumerableDioph.lean)
retains `encoded_evaln_natPrimrec` as a computational helper. Its
`Diophantine.rePred_dioph` now obtains a finite polynomial from `MRDP.mrdp`
and uses `dioph_iff_exists_fin_polynomial` to recover Mathlib's predicate
`Dioph {v : Unit → ℕ | v () ∈ S}`, including input zero.

The semidecider argument lives in `MRDP.mrdp`: fixed program code, the
primitive-recursive bounded evaluator, and `evaln_complete` express successful
execution as the existence of a bound whose encoded result is `1` (the code
of `some 0`). The core directly uses the finite-arity primitive-recursion
theorem, avoiding the old route through a paired scalar evaluator.

## From RE sets to one fixed universal quartic

The existing `MathlibDiophFinite` and `MathlibDiophBridge` adapters turn
Mathlib's functional `Dioph` representation into
`Jones1978.IsDiophantine`. Finite polynomial support removes the apparent
freedom to quantify an arbitrary witness index type; this is an actual
finite-witness theorem, not an assumption that Mathlib's witness type is
finite. Their validation is recorded in [STATUS.md](STATUS.md).

[RecursivelyEnumerableQuartic.lean](Diophantine/Paper1982/RecursivelyEnumerableQuartic.lean)
implements the composition with §5 compression. Its `rePred_quartic58`
statement supplies a normalized polynomial on `Fin 59`, of degree at most
four, representing a supplied RE set for every positive input. Coordinate
zero is fixed to the input, leaving exactly 58 natural witness coordinates.

That per-set existence statement is strengthened in
[UniversalQuartic.lean](Diophantine/Paper1982/UniversalQuartic.lean).
`rePred_quartic58_family` compresses the resulting quartic a second time,
now with starting witness count fixed globally at 58. The family is therefore
`ShortQuadratic.quartic58 z u y (L4 58)` for every set: only the three
positive index parameters vary, and `L4 58 = 5^59` is fixed. In particular,
the coefficient `2 * (2*z)^(L4 58 + 1)` is polynomial in `z` with a fixed
exponent; no variable exponent is being called a polynomial parameter.

The same module constructs a literal joint
`MvPolynomial (Fin 3 ⊕ Fin 59) ℤ`. It checks polynomial dependence through
the 46 existing residual expressions and the `IsPoly` adapter.
`specialize_jointPolynomial` proves equality with the explicit quartic
after fixing the three parameters, using polynomial extensionality on
natural assignments. `universal_quartic58` puts the single polynomial
quantifier before the quantifier over all RE sets. Parameter specialization
has total degree at most four in the input and 58 witnesses; the degrees
of the three index parameters are excluded, as the article specifies in §5.
No further existential witness is introduced by this uniformity packaging.

These RE/quartic and joint-polynomial declarations were included in the
original integration's focused compilation and axiom audit. Rebuilding and
auditing them after the transplant checks their use of the new RE bridge.

## Validation boundaries and article scope

The original extraction task verified the original/copied hash inventory, the 99
extracted lines, the single changed import, and complete umbrella coverage.
The source scan found no active proof placeholders or added axiom declarations
in the PAListCoding closure. Separately, serialized focused compilation and
one consolidated build passed. Its source inventory covered all 107 project
modules and the twelve vendor proof modules, with both umbrellas complete.

The repeatable [axiom audit](checks/RecursivelyEnumerableAxioms.lean) covers
the nineteen public theorems from that integration, ten vendor closure/trace
results, and Mathlib's primitive-recursive bounded evaluator, and now includes
three core MRDP declarations. At the original checkpoint, every one of its
thirty results reported exactly
`[propext, Classical.choice, Quot.sound]`. Run it again after a fresh full
build to check the current sources, alongside the MRDP endpoint audit:

```text
lake build
lake env lean Computability/HilbertTenthProblem/Lean/checks/MRDPAxioms.lean
lake env lean Computability/HilbertTenthProblem/Lean/checks/RecursivelyEnumerableAxioms.lean
```

The current receipt is in [STATUS.md](STATUS.md). Compilation, axiom
inspection, publication, and remote verification remain separate claims.

The RE bridge covers all natural inputs. The article's quartic membership
equivalences cover positive inputs, with normalization also asserted at zero.
The 58-witness bound and quartic degree do not include three index parameters
as witnesses and do not assert degree four jointly in all 62 indeterminates.

The generic representation route supplies the MRDP premise for the article
proofs. Their particular equations, universal pairs, operation counts, and
other structural claims retain their individual [STATUS.md](STATUS.md)
boundaries. No post-1950 result is introduced as an axiom by this integration.
