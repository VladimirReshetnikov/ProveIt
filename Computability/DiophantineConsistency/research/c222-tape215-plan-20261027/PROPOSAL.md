# Actual 215 tape, sparse states and boot: next internal checkpoint

27 October 2026. Read-only proposal; no new Lean source, overlay or compiler was
created. The proposed first pair is `ArithmeticMachineTape215` and its focused
Checks. It reuses the accepted **actual decimal** Graph215/Step215/Run215 packet,
and proves concrete sparse-state steps, the exact full boot, and arbitrary
internal continuations of that boot. It does not create another machine evaluator.

## Existing endpoints and the exact gap

`ArithmeticDagRuntimePerm222.seed_halts_iff` and
`ArithmeticControlBisimPerm215.halts_iff` already connect the actual C222
enumerator to the actual p215 control table, internally in every IΣ1 model.
Their common control-file seed is `[0,0,0,0,0,0,4,0,0]`; neither theorem supplies
a binary tape simulation. Runtime was accepted in `10100be9ca`; Bisim in
`17aee9ea3a`. Their exact accepted root packet pins are retained in the inventory.

Separately, `DiophantineConsistency.ArithmeticMachineRun215.run` already has a
fixed Σ1/Δ1 graph and total unique evaluation at every internal time. Its
`run_nat`, `run_represents`, and `haltingSentence_nat` bind the literal 715-digit
decimal machine, complete tape, and standard halting meaning. Its predecessor
Step215 covers all natural configuration codes. These accepted sources are
unchanged and must be reused. An initial narrow search of the BusyBeaver directory
missed these DiophantineConsistency modules; that preliminary conclusion is
explicitly superseded here.

`DecimalMachine215.commutes` gives every actual finite action under the sparse
K230-label map. `KSim`, `KTape`, `KHomeReady`, and `KBoot215` prove ordinary
Nat/list zipper statements. Their variable-length runs and register values are
not arithmetic-model theorems. The missing bridge is their concrete tape and
site behavior inside the existing decimal arithmetic run, followed by the
actual control/tape halting equivalence. No external Nat halting equivalence
may stand in for that bridge.

## State coding and finite boot data, rechecked

The composition `KDense215.expand (DecimalMachine215.toDenseNat i)` has 215
distinct live sparse labels. It excludes 230. The data audit records the full
list, all thirteen chunk source pins, and the exact sums; it is a read-only
data check, not a new Lean proof.

| Meaning | Sparse label | Dense index | Decimal index | Arithmetic state code |
|---|---:|---:|---:|---:|
| Blank live state | 0 | 0 | 0 | 1 |
| Dispatch after boot | 84 | 83 | 23 | 24 |
| Halt | 230 | none | none | 0 |

Thus a boot frame with first component 85 or 84 would be wrong for the accepted
decimal run. Define a finite inverse `decodeSparse : Nat → Option (Fin 215)`
from the actual `sparseExpand` list, and `sparseCode q = stateCode (decodeSparse q)`.
Prove both inverse laws on the live image and the concrete 0/84/230 cases.
Unsupported sparse holes also get default code zero: **do not state the global
equivalence `sparseCode q = 0 ↔ q = 230`**. Any converse is restricted to the
live-image-or-terminal support; an actual successful table row supplies live
support for its source. Transition targets are in that support. Arithmetic
halting is `first config = 0`, not `config = 0`; the final write and move remain
part of the tape on a halt transition.

The existing `KBoot215.block1` through `block13` have depths
`14,14,14,14,14,13,12,10,8,7,6,5,1`, whose powers of two sum to 95,714.
`KBoot215.boot` currently forgets the exact clock by concluding `Reach`; retain
the chunk equations to derive the exact numeric-run time. Its checked endpoint
is sparse state84, left `[true]` (the checkpoint has nine irrelevant trailing
zeroes), and

```
replicate 65 false ++ true :: sepsR
  ([0,0,0,0,0,0,4,0,0] ++ replicate 40 1).
```

There are 49 register blocks, 40 spare **ones**, and 208 significant right-half
bits. This is not the old252 state94/gap40/zero-spare convention.

## Proposed first pair and signatures

Imports only:

```
DiophantineConsistency.ArithmeticMachineRun215
BusyBeaver.ZFC.KBoot215
Foundation.FirstOrder.Arithmetic.Definability.Absoluteness
```

All model-level theorems use `[ORingStructure V] [V ⊧* IΣ1]`. The public fixed
graphs are declared independently of `V`. Estimated scope is roughly 300–450
main lines plus 55–80 focused checks; split the boot into a second small leaf
only if the concrete finite bridge warrants a separately reviewed checkpoint.

1. Define `frameSparse q L R = cantor (sparseCode q : V) (cantor L R)` and prove
   actual one-step binding for every literal sparse row. If
   `KTableCore.tm215 q bit = some (write,moveRight,q')` and
   `R % 2 = (bit.toNat : V)`, the existing `ArithmeticMachineStep215.stepValue`
   sends `frameSparse q L R` to

   ```
   moveRight: frameSparse q' (2*L + write.toNat) (R/2)
   moveLeft:  frameSparse q' (L/2)
                         (L%2 + 2*(write.toNat + 2*(R/2))).
   ```

   Here `L,R` are arbitrary internal elements; `q,q'` name fixed finite program
   states. Source membership is proved from the actual 226-row table, including
   all disabled rows; it is not assumed as a runtime invariant. Use the accepted
   `DecimalMachine215.commutes` and inverse state map rather than decoding the
   715-digit numeral repeatedly. Static lookup values can be lifted by their
   existing fixed graph and absoluteness. No primitive-equality or machine
   correctness oracle is introduced.

2. Define the actual-step `PR.Blueprint 1` iteration `runFrom time initial`,
   with zero equal to `initial` and successor equal to the **existing** Step215.
   Expose fixed Σ1/Δ1 graphs, total uniqueness, zero/successor/addition, equality
   `runFrom t 1 = ArithmeticMachineRun215.run t`, and preservation of the entire
   configuration when `first initial = 0`. All induction predicates are genuine
   Σ1 graph equalities with the initial code as a parameter; no arbitrary-predicate
   or standard-Nat induction is used for internal times. Old RunFromPerm252 is
   a proof-pattern guide only, not an import or a concrete semantic premise.

3. On ordinary list zippers, prove each successful `KBoot.lstep tm215` agrees
   with the actual decimal numeric step under `frameSparse` and `bitsCode`.
   Lift this identity through `KBoot.lblock` and run addition. Apply the thirteen
   already checked chunk equations and `fast215`, preserving the exact clock;
   do not rerun a monolithic 95,714-step kernel reduction. Define

   ```
   bootCode : Nat := cantor 24 (cantor 1 (bitsCode KBoot215.bootRight))
   standard_boot : ArithmeticMachineRun215.run (95714 : Nat) = bootCode
   internal_boot : ArithmeticMachineRun215.run (95714 : V) = (bootCode : V)
   ```

   The second equality uses `DefinedFunction.shigmaOne_absolute_func` for the
   same fixed actual run graph. It lifts one fully checked finite prefix, not
   an unbounded standard-Nat simulation. The boot tape formula and code24 must
   remain visible in the public endpoint.

4. Derive the genuinely internal continuation and halting endpoints:

   ```
   ∀ t : V, Run215.run (95714+t) = runFrom t (bootCode : V)
   (∃ t : V, first (Run215.run t) = 0) ↔
     ∃ t : V, first (runFrom t (bootCode : V)) = 0
   ```

   For a putative halt before 95,714, full-configuration absorption contradicts
   boot's nonzero first component24. Otherwise internal subtraction and run
   addition move the witness after the prefix. This has no supplied site,
   control simulation, root execution, or bounded-time premise.

Checks should expose actual graph witnesses, both left/right and halt actions,
zero tape halves, sparse0 versus arithmetic0, dispatch84/code24, unsupported
hole behavior without a false converse, exact boot tape and nonstandard-time
continuation. Ordinary source soundness, ZFC, Pell, and HA are outside this pair.

## Subsequent concrete site bridge, still unimplemented

The numeric bit convention is least-significant first. For arbitrary internal
`v,z`, the actual K register block `0 1^(v+1)` is
`block v z = 2*(Exp.exp (v+1)*(z+1)-1)`. Interpret the nine physical fields by
a fixed external fold and append an internally represented positive count of
identical value1 spare blocks. The K physical order `[2,8,1,4,3,7,0,5,6]` and
inverse `[6,2,0,4,3,7,8,5,1]` agree with `ArithmeticControlTable.registerOf`.

At a catalogue leaf `(Q,e)` with `Q.length ≤ 48`, the precise normalized entry is

```
frameSparse 84 1
  (bitsCode Q + Exp.exp (64+gap) * (1 + 2*blocks physicalFile spareTail)).
```

Here `gap` and the nine field values are internal. The boot has `gap=1` and
40 spare ones. The catalogue paths are the consumed false-first leaf bits;
normalizing different trailing-zero widths needs a proved numeric prefix
identity. The initial control1 path is all zeroes, so its normalized PC value
is zero; that finite binding still needs its own checked theorem.

The actual `KRuntimeCore` register semantics differ from old252: increment
appends one spare value1; positive decrement adds one to the free PC gap and
does not append a zero spare. PC overflow adds another gap cell. These effects
must be retained exactly. Required new internal obligations are actual-table
unary scans, the K mark/skip/return/carry/rollback box routines, the actual
`KHomeReady` shortcut, symbolic frame normalization (including head-on-left),
and a new arithmetic soundness theorem for the existing finite K symbolic
executor. Its `moved` flag is essential: accepted `runTo` checks start at false
and accept only after a positive-clock primitive, even for zero register/gap
cases. The old Nat `exec_sound` cannot discharge this obligation.

Once that soundness is proved, `KSites215.all_sites` supplies the complete
actual finite site certificates, and `ArithmeticControl215Table.table215_eq_catalogue`
binds all4,751 control rows. A represented Σ1 relation over valid numbered
controls, the coded physical file, internal gap, and internal spare count can
then establish positive-clock step and halt transport. The existing generic
`ArithmeticPositiveSimulation254.halts_iff` handles both directions at arbitrary
internal times with `Halted config := first config = 0`. The already accepted
Bisim and Runtime then compose to the actual decimal halting sentence. No
part of this later site bridge is claimed complete by the boot checkpoint.

Generic algebra in `ArithmeticTapePrefix254` and the lookup/action arithmetic
already imported by Step215 is reusable. Concrete `ArithmeticSitePerm252`,
`ArithmeticControlSimulation254`, register-box252, and bootstrap252 conclusions
are not interchangeable with K215; their labels, gaps and spare policies differ.
The exact later scan/box/site cache union remains to be audited before imports
or refreshes are authorized. The source-ZFC calibration and the final arithmetic
equation/HA proof obligations remain separate.

## Authenticated first-checkpoint inventory

`c222-tape215-plan-20261027/cache-plan.json` authenticates the reachable current
header DAG: **145 custom modules, including95 Foundation, 430 cached artifacts,
41 direct package boundaries with123 companions, zero refresh**. Only the
proposed new main/Checks would be freshly compiled after approval. The three
actual Graph/Step/Run215 primaries are the accepted independent root objects in
`/tmp/arithmetic215-root-peer-7nbm_glx`; the decoder uses its accepted byte-matched
author object. The KBoot chain comes from the accepted native source closure via
the subsequently reauthenticated NativeAdaptiveCurrent peer inventory. All125
source entries in the old arithmetic215 inventory (124 prerequisites plus the
fresh decoder) still match current bytes; no rebuild
of the generic252 lookup/step dependencies is proposed.

Every selected source, direct import header, cached artifact and first package
provider was rehashed. Final planning recorded1,666 observations over811paths.
Two package `.ir` companions not captured by the old machine receipt are
explicitly current boundary observations, not retroactive historical captures.
The first planner attempt stopped on a nested-versus-flat boundary record schema
before writing a plan; the failed log and script are retained. The second plan
used121 recorded companions and is preserved; the final adds the two disclosed
observations. No Lean compiler, cache copy, overlay, Git mutation, or dependency
build ran in this audit. Future execution retains the existing4.32 caps and
512MiB reserve.
