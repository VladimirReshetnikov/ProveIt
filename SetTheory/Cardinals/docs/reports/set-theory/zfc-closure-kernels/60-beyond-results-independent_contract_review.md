# Independent review of the relational and composable-box experiment

This review concerns `agent_root/relational_zones.cpp` and
`agent_root/compound_fold.py`, with the pinned 252-state old-label transition
table and original `Prog254.v`. It found no soundness defect in the reported
cap-8, fuel-1000 experiment. The result is a bounded checker search with no
survivor; it is not a proof that any 251-state machine is impossible.

## 1. Difference-bound invariants

The matrix orientation is consistent throughout: entry `(i,j)` bounds
`x_i - x_j`, and `x_0 = 0`. Thus the zero decrement branch adds `x_r <= 0`
to an existing natural-counter constraint, and the positive branch adds
`-x_r <= -1` before subtracting one. Increment/decrement translation adds the
register delta to its matrix row and subtracts it from its matrix column.

Both cap operations weaken constraints: a positive bound above the cap is
discarded; a negative bound below minus the cap is raised to minus the cap.
Restoring `x_r >= 0` is sound because every guarded source operation preserves
natural counters. Componentwise maximum is a sound join. Worklist termination
follows from the finite set of serialized bounds and monotone joins; soundness
needs the resulting postfix condition, not an assumption about convergence to
a best invariant.

The portable `verify_zones.py` supplies a separate check. It reads only
`program_cases.json` and a zone file. It does not import the generator or reuse
its rounded transfer. It closes each precondition, imposes the exact branch
guard, computes the **uncapped** translated postcondition, and verifies every
finite bound of the successor zone. It also checks that the entry zone
contains the all-zero valuation and that live zones enforce natural counters.

All four supplied zone files, with caps 1, 2, 8, and 32, pass. Each has 6,460
sites, 6,456 live sites, 8,391 guarded cases, 8,385 enabled cases, and 8,384
nonterminal successor edges. Each check verifies 226,735 finite successor
bounds. The excluded case IDs are exactly
`[8202,8203,8204,8358,8359,8360]`. One halt case remains enabled; an invariant
that admitted no halt case would require a much stronger argument here.

Evidence is recorded in `zone_audit1.json`, `zone_audit2.json`,
`zone_audit8.json`, and `zone_audit32.json`. This independent check assumes
the supplied source graph is correct. Source-to-graph extraction and the
blank-table bootstrap are separate audits performed by the root researcher.
Neither this checker nor the new invariant is a proof-assistant theorem.

## 2. Successive register-box calls

The symbolic register state records a cumulative displacement `delta` from the
register values at the beginning of the source instruction. If the initial
value is between `lo[r]` and `hi[r]`, the present value is bounded by the same
endpoints plus `delta[r]`. A positive decrement is justified by
`lo[r] + delta[r] >= 1`. A zero decrement is justified by
`hi[r] + delta[r] <= 0` together with the invariant that present values are
natural. Increment updates the displacement without an extra guard.

All 55 transition rows supporting the imported register-box contracts are
unchanged, including their target states. These contracts support repeated
calls with arbitrary natural contents of the other first-nine physical
registers and an arbitrary finite valid spare suffix. A positive decrement
may append a zero spare block. Treating that suffix existentially is therefore
sound: every call returns another suffix allowed by the next call's contract.
It is not necessary to preserve its length or exact cells in the symbolic
postcondition. This argument would fail for a contract requiring a fixed
suffix, an exact whole-tail equality, or arbitrary malformed suffix data.

The caller still checks its explicit header, path, marker, affine gap, and
control state. The existential treatment applies only to the physical spare
suffix, not to logical formula data or arbitrary tape cells.

The current code stores infinity as the finite integer `10**6`. It should use
an explicit infinity check if repurposed for much larger fuel or unrelated
input bounds. At cap 8 and fuel 1000, a cumulative displacement cannot approach
minus one million, and every allowed decrement is additionally guarded, so
this representation cannot falsely certify the reported zero tests.

## 3. Why using a source invariant need not be circular

For a changed TM, establish its blank bootstrap to the all-zero enumerator
root. Inductively suppose its current macro boundary represents a source
configuration satisfying the source invariant. A successful conditional
macro certificate then returns precisely the source successor configuration;
the invariant's postfix theorem applies to that successor. This induction
justifies reuse of the source invariant without first assuming correctness of
the changed machine. Positive literal progress prevents vacuous zero-step
simulation certificates.

The serialized invariants here start from all-zero logical registers. The new
relative-consistency seed theorem in `foundations_audit.md` does **not** make
them valid from nonzero startup formula data. A proposed dirty initializer
needs its own invariant entry proof or a newly generated invariant. It also
needs a complete valid binary frame; formula admission alone does not provide
that frame.

## 4. What the unsuccessful search establishes

The report records all 55,471 eligible uniform one-state folds checked at
cap 8 and symbolic fuel 1000, after all 8,385 baseline macro cases passed.
The eligibility restrictions protect the register-box implementation and
dispatcher: 221 states may be deleted, and each has 251 candidate existing
working-state replacements. There are 127,788 attempted case checks and no
surviving fold under this checker.

A rejected fold has failed to obtain this certificate. Fuel exhaustion,
unjustified box operations, unresolved affine lengths, and a missing halt row
are checker outcomes. They are not generally counterexample executions of the
concrete blank-tape machine. Projecting the DBM to per-register intervals
also discards correlations that could justify additional paths. Consequently
the experiment supplies no general 251-state lower bound, no exhaustive
search over possible machines, and no refutation of the broader semantic
seed method. Even a surviving local certificate would still need the altered
table's bootstrap and the complete simulation/calibration argument.

## Reproduction

```sh
python verify_zones.py --graph program_cases.json --zone zones8.txt --output zone_audit8.json
```

Only Python's standard library is required. The verifier uses explicit error
checks rather than Python `assert`, so running Python with optimization does
not disable its verification obligations.
