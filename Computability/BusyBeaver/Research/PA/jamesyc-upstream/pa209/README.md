# Nonhalting and PA-independence for a 209-state Turing machine

PA209 is an explicit two-symbol Turing machine that searches for a contradiction
in ordinary first-order Peano arithmetic (PA). It runs forever from a blank
tape. If $H$ is its exact arithmetic halting sentence, PA proves neither
$H$ nor its negation.

[Paper (PDF)](paper/pa209.pdf) · [Transition table](data/pa209.tm) ·
[Formal statements](docs/result.md) · [Reproduction](docs/reproduction.md)

## The machine

The tape is infinite in both directions and initially all zero. The machine
starts at state 0. Its 209 working states have two transition rows each.
State 215 is the halt label. After 58,210 tape steps the machine reaches the
register-program frame that starts the proof search at candidate 2.

## The proof

The register program enumerates finite words of proof commands and halts
when it derives a contradiction. Lean checks the source program, the startup
trace, and a positive-length tape simulation of every source instruction.
Soundness of the proof commands gives blank-tape nonhalting under PA
consistency.

In every model of PA, a coded PA refutation gives an accepted certificate, a
halting source execution, and a coded tape trace using the exact table.
Consequently PA proves $\neg H \to \operatorname{Con}(\mathrm{PA})$.
Gödel's second incompleteness theorem rules out a PA proof of $\neg H$
under PA consistency. Soundness of PA in the standard natural numbers
rules out a PA proof of $H$. Foundation's standard model supplies
consistency and soundness in Lean's metatheory.

## Paper-to-Lean map

| Paper | Lean |
| --- | --- |
| Machine and startup (§2) | [Literal table](M6/Literal.lean), [startup](M6/Startup.lean) |
| Physical simulation (§3) | [Source transport](M6/SourceTransport.lean), [runtime coverage](M6/Coverage.lean), [physical endpoint](M6/PhysicalEndpoint.lean) |
| Proof search and soundness (§4) | [AX formulas](M6/Source/ActualAXCode.lean), [logical endpoint](M6/LogicalEndpoint.lean), [PA consistency bridge](M6PA/Endpoint.lean) |
| Arithmetic trace sentence (§5) | [Exact halting formula](M6PA/Model/ExactHaltingFormula.lean), [statement correspondence](Solution.lean) |
| From refutation to halting (§6) | [Refutation transport](M6PA/Calibration/FoundationNativeRefutationTransport.lean), [scheduler](M6PA/Scheduler/SourceEnumerationFromTwo.lean), [trace](M6PA/RefutationHalting.lean) |
| Two-sided independence (§7) | [Internal consistency implication](M6PA/FinalEndpoint.lean), [independence](M6PA/TwoSidedIndependence.lean) |

The default Lake build includes the [PA209 proof](PA209.lean), the
[Palomar statement](Challenge.lean), and its [Solution](Solution.lean).
Run `bash scripts/check.sh` for source and table checks, or
`bash scripts/check.sh --full` to build and audit the proof.
