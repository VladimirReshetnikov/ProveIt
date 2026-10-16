# Closing the classical bridge in the named Tarski calculus

This package supplies three new Lean modules and the exact seven-module pinned
dependency closure needed to check them. The dependency pin is ProveIt commit
`4747142d5d15213eb711bdadfa3cc7e769fcb7a7`.

The completed endpoint is **ordinary first-order logical completeness of the
named-variable Tarski calculus**, with identity equality and genuine Bottom.
The final statements have no remaining `Kalmar.Classical` hypothesis. This does
not prove that a numerical formula encoding, literal axiom emitter, register
machine, or binary Turing-machine table implements that calculus.

## Reproduce

Use Lean 4.32.0, with Python's standard library:

```sh
python reproduce_lean.py --lean /path/to/lean --output verification.json
```

The driver checks the Git blob hashes of all seven original dependency files,
freshly compiles all ten modules into a temporary directory, and audits the
printed axiom dependencies of 17 theorem roots. It rejects `sorryAx`, custom
axioms, unexpected dependencies, a missing endpoint audit, or a compilation
failure. It does not download packages or reuse previously compiled `.olean`
files. `lean-bridge-verification.json` is the preserved original successful run;
`packaged-verification.json` records the subsequent check from this delivery
directory. The source hashes in both runs agree.

The package layout deliberately retains the generator and driver's original
relative paths: the namespace source tree is the inner `lean/` directory.

## Three additions

| Module under `lean/BusyBeaver/ZFC/` | Contribution |
|---|---|
| `Lukasiewicz.lean` | Explicit derivations of K, S, and Peirce from the one pure implicational Łukasiewicz axiom and modus ponens. |
| `TarskiClassicalBridge.lean` | Derivation of Bottom elimination from rho6 and K/S; a closed `classical_from_rows`; a counterinterpretation showing rho8 alone cannot give Bottom elimination. |
| `TarskiCompleteClosed.lean` | Discharges the classical assumptions of the pinned completeness theorem and exports the two closed endpoints. |

The generic implicational axiom is

```
(((p -> q) -> r) -> ((r -> p) -> (s -> p))).
```

It is Polish `CCCpqrCCrpCsp`. The derivations have 13 intermediate/result
lemmas and 202 displayed proof rows, of which 95 are modus ponens steps.
Every generated Lean term is checked by the kernel; no semantic truth-table
claim substitutes for the derivation. The interface is polymorphic in a
carrier, an implication operation, and a theorem predicate. In particular,
it does not assume implication is injective.

`generate_lukasiewicz.py` reconstructs `Lukasiewicz.lean` offline from
`metamath-proof-steps.json`. That generator and its JSON data are untrusted:
their only role is to propose the explicit terms checked by Lean. The proof
tables are the public-domain Metamath work of Larry Lesyna and Jeffrey P.
Machado, based on Łukasiewicz's 1948 result. Each theorem and JSON record carries
its exact public source URL. The principal sources are:

- https://us.metamath.org/mpeuni/impsingle-ax1.html
- https://us.metamath.org/mpeuni/impsingle-imim1.html
- https://us.metamath.org/mpeuni/impsingle-peirce.html
- https://us.metamath.org/mpeuni/tarski-bernays-ax2.html

## The Bottom issue

Pure implicational classicality cannot by itself identify a distinguished
formula with falsity. For any target A, let
`Q = forall i (forall i A -> Bottom)`. Row rho6 provides `(Q -> Bottom) -> A`.
K gives `Bottom -> (Q -> Bottom)`, and the K/S composition derivation gives
`Bottom -> A`. This uses four axiom instances and three applications of modus
ponens; no generalization is required for this bridge.

The formal counterinterpretation assigns true to Bottom, false to atoms,
ordinary Boolean implication to the implication constructor, and identity to
quantification. Rho8 remains valid, as do MP and GEN, but Bottom elimination
fails. The new bridge therefore relies on the actual rho6 row as well as the
implicational reconstruction.

## Exact audited endpoints

The fifteen audited roots in the two reconstruction/bridge modules are
axiom-free. The two final roots are

```
SetTheory.BusyBeaver.ZFC.Tarski.completeness_closed
SetTheory.BusyBeaver.ZFC.Tarski.theorem_iff_semantic_consequence
```

The semantic premise requires every theory axiom to hold under every total
variable assignment; open axioms therefore stand for their universal closures.
The displayed Lean quantification permits an empty carrier, but there is then
no total assignment `Nat -> D`, so that case is vacuous. The countermodel
constructed by the completeness proof is inhabited.

Their complete axiom lists are `[propext, Classical.choice, Quot.sound]`, the
standard Lean foundations used by the imported classical completeness proof.
There are no custom axioms, `sorry`, or `native_decide` dependencies. Six
pre-existing unused-variable lints in the pinned `TarskiComplete.lean` are
recorded in the logs; the new modules compile without warnings.

## Repository integration

Copy the three additions into
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`, preserving their filenames.
The seven other `.lean` files are a reproducibility snapshot, not proposed
replacements. `tarski-documentation-correction.patch` corrects two pinned
headers that prematurely described the bridge as already closed; it does not
change existing theorem statements. New callers may import
`BusyBeaver.ZFC.TarskiCompleteClosed` and use its unconditional endpoints.

`audit_results.md` gives the detailed audit and derivation. `zfc_internalization.md`
explains the separate uniform-model route to a ZFC internal consistency
calibration and the unproved checker/runtime/compiler interfaces that remain.
