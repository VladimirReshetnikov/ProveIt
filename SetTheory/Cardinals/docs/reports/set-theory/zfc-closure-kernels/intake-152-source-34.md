# Intake 152 / manuscript09 / local34

Verdict: accept as an addition. The entire article, finite-kernel and independent-review notes, source/endpoint audit, proposed Coq wrapper, complete theory generator/ground checker and initializer/quotient/reproduction code were read. The ordinary mathematical construction and finite engineering claims pass review. No current repository assertion requires retraction, and no new calibrated machine below253 states is supplied.

## Identity and provenance

Title: *Small Turing Machines for the Consistency of ZFC*. Arrival `da6dabcd8976acf94c4f3652ed3eeae5713b3d2a`, archive `zfc_small_machine_research_20261016.zip`, internal root `zfc_small_machine_research`; placement `b123527ff4`, prefix `34-k12-`. ProveIt pin `d74c63b0c8d4f35597f1bd5976d941b9f104f94e`; upstream main `297ab8df7e5de329605c3875b4934643b371a5e3`; public253 `0d544f2a2e3c18f12278441a74b7879f31cbe856`. Its CI excerpt concerns synthetic merge `26bd0b2beeed5c3dd88511e39acd604c235e2f1c`; that historical public evidence is distinct from this intake's executed checks.

Friedman's finite assignment/class idea is explicitly prior work; the new component fuses projection into Separation/Collection and gives its own12-axiom/28-clause presentation. Mira/Wade/Jeff/mira-emmy machinery, source21 initializer and earlier206/202-node inputs retain separate attribution. The borrowed minimal compiler closure and notices suffice for all advertised Python regeneration. A Coq wrapper build requires the separate full pinned PR checkout. No necessary Python input was missing; no blanket new license over borrowed material is inferred.

## FAK12 mathematical review

The one-sorted nonempty language uses genuine equality, membership E, class incidence epsilon, constants e/I, and initial functions V/C/Pair/Union/Power. All selectors, assignment objects and class codes share the same domain. A1--A4 give coherent coordinate update, NAND, membership atoms and existential binding. A5--A10 are ordinary Empty, Extensionality, exact Pair/Union/Power and successor Infinity. A11/A12 fuse evaluation at e and at distinct e/I coordinates into Separation and partial Collection. Empty plus Infinity gives e≠I. No external-subset coding or expanded-language comprehension is assumed.

The lower direction is noncircular. Exact singleton formation is injective and e lies outside its range, supplying arbitrarily many distinct selectors before any schema recovery. Induction on a fixed pure-membership formula gives its class code for every assignment object; Extensionality erases equality atoms using fresh membership quantifiers. Finite C updates store arbitrary parameters. A11 gives full Separation; A12 gives partial Collection and, with Separation, functional Replacement. The E-reduct has ZF without Foundation/Choice. The usual relative-consistency interpretations provide the remaining consistency comparison; Foundation is not asserted directly of the reduct.

For the upper direction, Con(ZFC) gives an arbitrary countable set-coded model, not necessarily transitive or omega-standard. V and C use the same internally definable normalization of finite partial maps, including invalid assignment codes and nonstandardly finite maps. An ambient surjection from the countable model domain onto its E-definable subsets supplies epsilon. Definability of V/C gives the three closure axioms. Each fixed class code has an ordinary finite E-definition, so the model's actual Separation/Collection verify A11/A12. No internal definability of the external enumeration or satisfaction class for the expanded language is required. This gives the stated ZFC-formalizable model construction, without asserting a serialized proof translator or a Lean theorem.

All28 emitted clauses match those12 axioms. The Extensionality witness really enforces XOR for unequal objects; Union and Power witnesses have the necessary two directions. Collection's witness depends on A,b,t,x and can omit the antecedent witness y: once the fiber is nonempty one output works for all such y, and otherwise a nonempty-domain default suffices. Skolem expansion is justified in the stated ambient ZFC metatheory. Exact metrics are62 literals,244 term occurrences, two constants,15 proper functions, two non-equality relations, at most five universal variables and term depth3. These are syntax metrics, not TM states.

The finite ground decision procedure enumerates partitions of all observed subterms, checks function congruence and predicates on argument classes, and extends unobserved function tuples by a default element. Cyclic term identifications are permitted; an occurs check would be wrong. Fairly grounding all colliding substitutions and restricting a compactness model to its constant-generated substructure establishes the ideal semidecision specification. Tiny diagnostics are not a whole-kernel consistency test, and no such search was run.

The reported local transcription issue was independently confirmed on the primary *Impossible Counting* PDF, printed/physical page34: the first displayed T[3,8] prefix omits z and includes unused v. This is a reason to reconstruct that block, not a refutation of Friedman's overall theorem. FAK12 and its clauses are derived independently of that display.

## Initializer and quotient review

The contiguous unary-counter invariant is complete: after k iterations the marker has moved km left, exactly n−k counter ones remain, fixed header/register data are unchanged, and every other cell is blank. The next register block always contains a one, including a zero value, so the final test is valid. The standalone contract is gap n(m+1)+3, states S+n+m+33, moves S+35+8n+(m+1)n(n+2). Shared cleanup inserts a sentinel and uses explicitly checked unchanged runtime rows; its corresponding constants are5,32,57. The exact family optimization and its square-root formulas are correct within those constructor families, not global lower bounds.

The state quotient has a total rowwise homomorphism with terminal mapped only to terminal. It therefore preserves every exact step, whole tape, head and halting time on every input. The independent verifier reparses both tables and checks every row equation. It does not rely on the symbolic register oracle. The three savings in these controls come from the generic decrement/break scan and two writer/stride identifications; neither published254 nor public253 has a nontrivial exact quotient.

For original219/seed0 the comparison is previous raw341→quotient338 versus new shared raw337→quotient334. The advertised341→334 combines four raw initializer states and three quotient states; quotient-to-quotient saving is four. Seed2 is343→340 versus339→336. Final206-node controls are321/323;202-node decoder controls309/311. The selected gaps, literal times and full finite tape supports are included. Those backends differ from public253, so seven states cannot be subtracted from that machine. Seed0 is a compiler control, while seed2 is the proof-enumerator seed.

## Executed checks and adapter correction

The extraction was untouched; execution used independent scratch copies. Bulk manifest checks were omitted in memory, with functional generated-data/transition/certificate/whole-tape comparisons retained. The final permanent worker is file-specific and deliberately leaves `engineering/reproduce.py` unchanged.

* Fresh-copy `verify_artifacts.py`: PASS,0.946s. All three finite-theory files regenerate exactly, all eight ground diagnostics and the eight-row Extensionality table pass, all18 saved quotient certificates and36 complete raw/quotient boots pass, and both published-table negative controls are checked.
* Full `engineering/reproduce.py` was executed. All18 combinations of three DAGs, two seeds and three initializers regenerate; every quotient passes8391 affine cases; both raw and quotient boots compare their whole finite support, head, state and exact time. Boundary checks cover432 standalone and432 shared cases for n,m=1..12 and three register vectors. Both published-table negative controls regenerate and have no nontrivial quotient. All61 regenerated tables/certificates/evidence files match delivered bytes exactly.
* The first129.293s regeneration used an overly broad scratch adapter. Its `upstream`-loop heuristic mistakenly skipped the two functional published-table regeneration loops, although the18 variant checks and the independent saved verifier passed. That initial run alone was incomplete. The heuristic was narrowed, the entire engineering reproduction rerun, both controls included, and all61 files compared. The permanent worker has no AST patch at all for the engineering reproducer; this identity was checked, and its other quick paths were rerun from new original copies. No final claim relies solely on the incomplete run.

[Review evidence](data/intake-152-source-34-review.json) records the full18-control ledger and correction. The delivered wrapper `FullZFC253.v` is a sound source-level composition using the exact Foundation-qualified predicate and existing refutation equivalence. Its checksum-only provenance commands were not treated as kernel proof. No Coq build, full consistency search, arbitrary-register compiler theorem or FAK12 binary compiler was run or claimed.

## PDF, source context and reproduction

Three shell-escape-disabled pdfLaTeX passes PASS:25 physical pages,498789 bytes, all fonts embedded, no warnings, undefined references or layout overflow. All pages were rendered and visually checked; the12-axiom page11 was enlarged and clean. [PDF evidence](data/intake-152-source-34-pdf-qa.json).

Historical gaps are compared with the current tree rather than repeated as current failures. Named logical completeness and exact numeric named transport already exist. CP/GIC quotient ZF0, including ordinary Infinity, is now present; decoded semantic translation/freshness and actual binary register/PC boxes extend the boot through RM331. Newly merged L2 AX evaluation identifies the original DAG's emitted stack/gate. None formalizes FAK12 or eliminates complete enumerator/register/decoder/binary and Foundation/Choice/internalization obligations. The whole-machine goal remains open.

Recover the original hierarchy before execution. The host helper `--run 34` runs the finite artifact verifier. The stronger regeneration command is:

```sh
python3 -B HOST/code/intake_152_backend_adapter.py --source 34 \
  --root RECOVERED_SOURCE34 --script engineering/reproduce.py -- \
  --output NEW_SCRATCH_CONTROLS
```

This source has no bulk manifest loop, so the worker leaves its AST unchanged, including both published-table controls. No delivered Coq/Lean patch should be installed automatically over the newer project.
