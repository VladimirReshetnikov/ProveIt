# Independent read-only review: internal C222 equality core

Reviewer: `complemented47_review`. Result: PASS within the stated scope;
no mathematical, source-binding or recorded-provenance correction found.
I read all127 main lines, all48 check lines, the complete author receipt,
replay inventory and all three execution drivers. I did not compile,
execute those drivers, modify frozen sources or objects, or commit.

| Artifact | SHA-256 |
|---|---|
| `ZFCinPA/ValidatorEqualityCore222.lean` | `caa7d6c534c5f7a31ec6e5d314be364c57dcefe8d577b0eba86db0eaea4af9ce` |
| `ZFCinPA/ValidatorEqualityCore222Checks.lean` | `88439cf53e43f7d7bbc074eed0c34c1097ae72c5e476cb990f68252397cf79d8` |
| author receipt | `aa385cc7d43f4799af4a2f863a8029741d1e11faf4c7013cd40e485fba36a45a` |
| replay JSON | `95ea506509731f5fb3f698b929414c0d1a840883e6e1c8692953be9ebdd42893` |
| pre-execution input inventory | `689b53312074117698b0b2510b1ba4e429f9e25725b5e556cc0c6c6fcab0754e` |

## Exact mathematical scope

All general theorems have precisely an arbitrary `ORingStructure V`
and the instance `V` models IΣ₁. Their predicate is the actual
`ValidatorProvability222.CProv p := ∃ code, ArithmeticHistory222.value code=p+1`.
The frozen parent supplies actual numeric proof witnesses for MP, GEN,
rows1/2/6/8, changed growG and gated helper-free bundle. The result is not
restricted to standard natural inputs. No derivability or truth assumption
is imposed on its arbitrary parameters.

The three logical lemmas `contrapose`, `all_ex` and `ex_mono` use finite
`Kalmar.Der` lists with exact hypothesis discharge. `ex_mono` additionally
takes the displayed `CProv (wim a b)` hypothesis. The five main deductions
then establish reflexivity, the helper, helper specialization, rho7, and
membership vacuity. Only membership vacuity adds premises, exactly `c≠a`
and `c≠b`; equal a,b and zero c remain admissible if those gates hold.
Reflexivity, helper, specialization and rho7 have no positivity or
freshness restriction at all.

I traced every MP and deduction application. The root finite convention is
major premise first; `d0` is the current head and `d1` the next hypothesis.
The reflexivity proof sets r to the literal numeric `wel x x`, applies
growG twice to the same equality hypothesis, lifts through the represented
existential supplied by rho1, and eliminates `∃r ∀r` using rho6. It does
not silently specialize an arbitrary universal. The helper follows from
that reflexivity; the separate helper-specialization proof uses quantified
K, rho1, existential monotonicity of the now-derived helper and rho6.
Only then is the final quantifier in growG removed to derive rho7.

For membership vacuity, the parent seed is exactly
`wim (wim (vrel a b c) (nks a b c)) 1`. The finite certificate
`¬(A→B)→A`, using the established C222 Peirce/ex-falso witnesses, projects
vrel. No semantics of nks, no old bundle, and no seed-validity theorem
is required. Relative falsity stays numeric1 throughout. The checks expose
the expanded membership formula and both legal gate edge cases.

The existing Nat file `KEqCodes222` is a matching derivation pattern only;
it is neither imported nor invoked. The one Nat corollary instead applies
the new internal rho7 endpoint and the actual `cProv_nat_iff` binding.
The identifier `ArithmeticTemplates254.rho7` is the unchanged constructor,
not an assumed C254/C222 rule. Generic Kalmar works for any implication
operation with the supplied witness closures; no constructor injectivity,
freshness or standardness is smuggled into that use.

## Source and provenance review

I reread the complete direct `ValidatorProvability222` source, full generic
Kalmar and Nat guide, actual growG/seed circuits, and the used arithmetic
constructor/template contracts. Relevant pins are:

| Contract | SHA-256 |
|---|---|
| `ValidatorProvability222.lean` | `a3b50d8088d288ee951f2a9612e624e54ea78814151aaa3a2acc083242ac78b2` |
| `Kalmar.lean` | `3cf0caf5187aa99790d83ac1b482dbc228942cc6308a752ae2b7f980984381b4` |
| `KEqCodes222.lean` (guide only) | `1e2e768af99cbf3fe1cae0f4f41e93c229e77f8ea4937ceab9884a93ff8071cb` |
| `ArithmeticCode254.lean` | `2edf178b0061838b13299f1332d65c4fc3194207cbd0e761f129a7bcc36bdff0` |
| `ArithmeticTemplates254.lean` | `2031511caadb7bf794d190cea99bedfa32022197f64612cb270daceee986f65f` |
| `ArithmeticSeedTemplates222.lean` | `d0f878669c9f8c8c9d94bccf451544aba6f7304368355f0bba440999ce342a59` |

Independent read-only hashing verified587 recorded comparisons: all123
custom sources (95 Foundation),408 recorded object companions,38 explicit
external roots, compiler/manifest, parent receipt, drivers, inventory,
final source snapshots/objects/logs/timings and historical run JSON. I also
reparsed every selected source's imports and compared the complete lists
to the inventory; the embedded inventory equals its pinned private JSON.
All comparisons passed. The private overlay is
`/tmp/equality222-controller-0bdkt7ff`; its search path contains that
authenticated custom overlay and explicit package roots, not the shared
project object directory.

The recorded first main/check pair has two exit codes0 under Lean4.32.0,
`-M6000 -j1 -DElab.async=false`. The main log is empty. The checks contain
the eight expected reports, each restricted to `propext`, `Classical.choice`
and `Quot.sound`. These are independently inspected author-run records,
not an independent fresh replay by this reviewer. The package boundary
and cached Foundation provenance retain the parent inventory's scope;
hash agreement is not a fresh proof of that whole dependency closure.

I previously reviewed the new constructor/history/provability dependencies
and authored separate equation/native work; I did not author this equality
packet or its underlying C222 represented checker. This review establishes
the claimed finite internal witness deductions. It does not establish
semantic seed validity, internal inter-calculus equivalence, machine runtime,
an HA proof, or the final requested HA consistency equivalence. C222's
classical finite certificates add no inference rule to the separate HA calculus.
