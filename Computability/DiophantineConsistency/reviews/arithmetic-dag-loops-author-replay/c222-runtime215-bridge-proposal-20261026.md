# Actual C222 scheduler to literal decimal215: internal runtime audit

26 October 2026. Controller-certificate agent; read-only source/cache investigation.
No Lean compilation, object replacement, source-program execution, archive builder,
or Git operation was performed. This is a proposal, not a runtime-equivalence theorem.

## Exact missing target

For every arithmetic model `V` of `IΣ1`, with both existential times ranging over
**all elements of V**, the required bridge is

```lean
(∃ n : V, ArithmeticEnumRunPerm222.run n
    (ArithmeticEnumStepPerm222.liveValue 0 4 0) = 0) ↔
  ∃ t : V, ArithmeticCantor.first (ArithmeticMachineRun215.run t) = 0
```

For Type0 models, the left side is now linked to existence of an actual
`ArithmeticHistory222.checkDef.val.Evalb ![code,1]` witness by
`ArithmeticEnumSoundnessPerm222.refutation_iff_zero_work_halts`; that packet
was authored by this reviewer and is undergoing root independent acceptance.
The right run is already the fixed represented decimal-machine run, not an
abstract machine parameter. `ArithmeticMachineRun215.runDef` and `runDeltaDef`
are total/unique at internal times; its `haltingSentence` is the exact closed
Sigma1 sentence. Its `run_nat`, `run_represents` and `run_halt_iff` currently
identify standard Nat behavior only. Run totality does not prove this bridge.

After both all-model directions, Type0 arithmetic completeness can give an
actual `IΣ1` derivation of the equivalence of the two closed sentences, followed
by PA weakening. That would still not fill the separate source-ZFC calibration,
equation/Pell arithmetization, or final HA proof-existence obligations.

## What the current 215 endpoint proves

The maintained source chain is literal and valuable, but external:

* `KEndpoint215.p215_boot_iff` combines `KSource215.p215_halts_iff`,
  `RMEquiv.path_iff_iter` and `L2Perm.dagPerm_seed_iff` at the actual seed.
  Its configurations have ordinary Nat registers and its runs are Nat runs.
* `KSource215.pathDagPerm = RMEquiv.ofDag DagPerm.dagPerm 487`;
  `KSource215.p215` has root178/fuel179 and 4,751 leaves. Its current normalized
  certificate has 1,426 pairs, verified in sixteen chunks. This is excellent
  finite data; `RMNormalizedBisim.WithDecoder.check_halts_iff` is not yet an
  arbitrary-internal-arithmetic simulation theorem.
* `KEndpoint215.blank_halts_iff_zfc_refutation` combines standard register,
  tape and set-theoretic endpoints. It cannot be supplied as an internal PA
  theorem about nonstandard computation codes.
* `KBoot215.boot` is the fixed 95,714-step bootstrap: sparse state84, one true
  bit on the left, gap65, physical registers `[0,0,0,0,0,0,4,0,0]`, then forty
  spare blocks holding1. `KSites215.covered` checks the current program sites.
  Their concrete execution soundness is presently over Nat/list tapes.
* `KDense215` and `DecimalMachine215` supply exact finite machine relabelings,
  including the 715-digit decoder and all430 actions. Their standard machine
  conjugacies do not alone transfer represented executions in arbitrary models.

The root `verification/k215/README.md` explicitly describes its conclusions as
external proof-assistant theorems and says it supplies neither an internal PA
proof nor a derivation encoded in ZFC syntax. Historical proposal copies under
that directory were treated as references only, not imported or executed.

## Genuine reusable internal interfaces

1. `BusyBeaver.ZFC.ArithmeticControlFile`: nine-field arithmetic file encoding,
   read/write laws and `liveValue c file = cantor c file + 1`. This is generic
   numeric infrastructure, with zero reserved for halt.
2. `ArithmeticControlTable`: fixed finite `List Row` determines a Sigma1 step
   and `controlRunDef` (arity3). `spec`/`spec_get`, `controlRun_zero`,
   `controlRun_succ`, `controlRun_add` and `controlRun_halted` hold internally.
   Invalid row0 is not silently a supported current program instruction.
3. `ArithmeticDagRun`: `Occ p rows fuel edge pc exits` is a **finite external
   certificate** of a block in a concrete row table. `IRun p rows run edge x X y`
   gives an existential **internal** clock at every such occurrence.
   `run_iterate` proves counter loops by genuine Sigma1 induction. Occurrence
   fuel being a standard natural number does not bound runtime or register values.
4. `ArithmeticControlBisim.halts_iff_of_check`: a finite checked offset-segment
   certificate gives two-sided internal halting equivalence of represented
   control interpreters. Current concrete instantiation is Rotation240, not215.
   The normalized tree-certificate format in `KSource215` is different; a
   checked conversion/reindexing or an internal normalized-checker theorem is
   still required. No automatic format compatibility is claimed.
5. `ArithmeticPositiveSimulation254.clock_reach` and `halts_iff`: generic
   Sigma1 cofinal-clock transport in arbitrary `IΣ1` models. Each nonhalting
   logical step must take a **positive** internal binary clock; the relation
   must imply active logical/binary states, and binary halt must be absorbing.
   The reverse direction reaches beyond an arbitrary proposed binary halt time.
   A standard-Nat simulation or an unbounded arbitrary-predicate induction is
   not a substitute for these explicit obligations.

The physical maps agree: `Permutation252Frame.physOf` and `KSim.physOf` are
`[6,2,0,4,3,7,8,5,1]` below9, with inverse order `[2,8,1,4,3,7,0,5,6]`.
This can be checked without assuming any old machine semantics.

## Smallest recommended first implementation

New `ArithmeticDagLoops` plus focused Checks, importing only
`ArithmeticDagRun` and `DagPerm`. Expected about180–230 main lines plus50
checks, without changing any old module. Factor the three numeric loop proofs
currently specialized in `ArithmeticL2Lib254` into genuinely generic laws.
Do not import that old semantic module or its `IR` abbreviation.

For arbitrary fixed `p : RMDag.Prog`, `rows`, represented Sigma1 `run`, and
the exact generic `run_zero/run_add/run_one/spec` contracts, prove:

```lean
transfer (hn : p.nodes n = (.decnz src, .node m))
  (hm : p.nodes m = (.inc dst, .cont 2)) (hsd : phys src ≠ phys dst) (x : V) :
  IRun p rows run (.node n) x .normal
    (lupd (lupd x dst (lreg x dst + lreg x src)) src 0)

copy2 (hn : p.nodes n = (.decnz src, .node m))
  (hm : p.nodes m = (.node m', .cont 2))
  (hm' : p.nodes m' = (.inc d1, .inc d2))
  (h1 : phys src ≠ phys d1) (h2 : phys src ≠ phys d2)
  (h12 : phys d1 ≠ phys d2) (x : V) :
  IRun p rows run (.node n) x .normal
    (lupd (lupd (lupd x d1 (lreg x d1 + lreg x src))
      d2 (lreg x d2 + lreg x src)) src 0)

clear (hn : p.nodes n = (.decnz r, .cont 1)) (x : V) :
  IRun p rows run (.node n) x .normal (lupd x r 0)
```

Each result is obtained from `run_iterate`, using the internal source register
as iteration bound. Its invariant is a represented file with source reduced by
the current index and destination(s) increased by that index; no Nat induction
on an internal counter, standard-list premise or supplied loop correctness.
Handle zero counts as well as arbitrary positive/nonstandard counts.

Include exact current `DagPerm` corollaries: transfer node197 via191 (`p1→p2`),
copy node192 via187/188 (`ac→s1,s2`), and clear node214 (`tw→0`). These node
equations survive the current `Dag219`, `DagDom` and `DagPerm` overrides and
use no old-254 semantic theorem. A local represented table can be used in a
focused check to discharge an actual `Occ`, rather than leaving every example
vacuous when a row table has no occurrence.

This first leaf deliberately retains the precise generic row/interpreter
contracts and finite occurrence interface. It is a useful internal subroutine
proof, **not** a scheduler-to-machine equivalence and not a supplied simulation
premise in disguise. The next checkpoint must construct the actual whole
`DagPerm` table/root occurrence; it cannot infer that from these conditional
occurrence theorems.

## Subsequent substantive obligations, in order

* Construct the fixed `DagPerm` control catalogue and prove its actual root
  `Occ` with exits restarting the root. Use bounded finite data/check chunks
  or a structural table-construction theorem, not one unchecked external table.
  Then adapt the actual logical-register macros and root command dispatch,
  including NIP0/DROP1/MP2, old-counter AX parameters and the two physical reads.
  The new seed has `np=4`, all other fields0; old `ArithmeticL2Endpoint254`
  starts at `np=3,p1=3` and is not the desired endpoint.
* Bind its root relation to the accepted actual `ArithmeticEnumStepPerm222`.
  A natural state embedding is physical file
  `[stack,pointer,top,counter,0,0,candidate,cache,0]` at control1. Prove the
  actual step/halt contracts and positive elapsed clock. Use the generic
  cofinal-clock theorem for **both** all-internal halting directions.
* Connect this table to the literal rotated `p215` table using an actually
  checked certificate with proper pointer/exit/offset interpretation. The old
  Rotation240 certificate and C254 endpoint are not substitutes.
* Represent arbitrary-start execution of the exact decimal215 step, with
  additivity and whole-config halt absorption. Its blank specialization must
  equal existing `ArithmeticMachineRun215.run`. Internalize the current
  K symbolic boxes/site checker on nine arbitrary internal registers, arbitrary
  spare counts and gaps; retain complete tape encodings, positive clocks and
  the actual bounded control catalogue. The Perm252/Rotation240 arithmetic
  site modules are blueprints, not executable215 contracts.
* Bind sparse K states, dense215 and decimal215 state numbers by their actual
  finite relabelings, preserving state-code0 and the final write/move on halt.
  Lift the fixed bootstrap without assuming an arbitrary standard simulation
  is arithmetically valid. Then instantiate positive-clock transport and form
  the exact closed sentence equivalence above.

All these tasks are independent of the remaining source-ZFC axiom-image gap.
Even completing this runtime chain would not, by itself, prove the requested
HA equivalence for the displayed polynomial.

## Source/cache preflight for the first leaf

`c222-runtime215-cache-audit-20261026.json` records the current complete header
closure and all selected source/object hashes. Comments were removed before
reading imports (several old comments contain prose beginning with `import`).
Counts:136 custom,95 Foundation,39 direct external boundaries;130 source-matched
reusable modules /415 recorded artifacts, plus six explicit fresh prerequisites:

`ArithmeticControlFile`, `ControlCatalogue`, `ArithmeticControlBisim`,
`Permutation252Frame`, `ArithmeticControlTable`, `ArithmeticDagRun`.

Their historical leaf sources and objects still hash correctly, but their
historical transitive project-source versions include changed `Code254`,
`RegisterPath`, `RMDag`, `RMEquiv`, `RMBisim` or `SiteCoverage` sources.
Those six old objects are therefore recorded as **excluded candidates**, not
silently reused. Current accepted native, decimal-arithmetic and Enum providers
cover the other modules; the unchanged Table253/zipper subclosure is separately
source-checked against its executed historical record. The only external-name
addition to the Enum closure is toolchain `Lean.Elab.Tactic.Omega`, pinned from
the accepted arithmetic215 boundary. No Foundation refresh is indicated.

This is an authenticated candidate inventory, not a compiled overlay. Before
any execution, root must authorize the six unchanged-source refreshes and new
pair, with complete relevant source/driver reads, private regular outputs,
Lean4.32 `-M6000 -j1 -DElab.async=false`, and512MiB reserve. The historical
passes remain historical; no whole Foundation/package rebuild is claimed.

Review scope: the generic positive-clock theorem, DagRun interface/induction,
current endpoint and seed/physical layout were read; ControlTable/Bisim and
L2/site families were inspected at the relevant definitions/contracts/proofs.
The entire huge finite215 source/site/check families were not independently
reread or executed in this audit. Their existing recorded finite verification
does not close the missing internal simulation.
