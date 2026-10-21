# Shortening the certified K215 proofs

Pinned repository: `VladimirReshetnikov/ProveIt`, commit `c9dc79323429112c698100f3226a6e4d56c8b782`.

## Main recommendation: prove symmetry once, not every instance twice

The most immediate improvement is mathematical, not a faster evaluator. Lean's
`RMOffsetBisim.OBisim` is already a symmetric segment-bisimulation specification,
but its public theorem only transfers halting in one direction. The instance
therefore materializes and checks both a 2,240-entry certificate and its mirror.

For a relation S(A,B,z), define its reverse by Sᵒᵖ(B,A,z) = S(A,B,−z).
A good segment contains the two segment executions and the identity
δ(z,i)+count(left,i) = count(right,i)+δ(z′,i).
Swap the executions, negate both offsets, and rearrange that identity. At a
matched decrement test, δ(z,r)=0 implies δ(−z,r)=0. A matched halt remains a
matched halt. This constructs the reverse OBisim without evaluating another
certificate. Apply the existing one-way halting theorem in each direction.
This works for all offsets, not merely this candidate's zero-offset records.

`OffsetBisimSymmetry.lean` gives a 61-line proposed proof (including comments and
imports). `proposed/` contains the resulting replacement instance files. The
statement `p215_halts_iff` remains unchanged, as do the final machine and ZFC
endpoint. There are no axioms, sorry/admit, unsafe computation or native_decide.
The reverse data and sixteen backward check imports are removed.

**Verification boundary:** this mathematical derivation has been reviewed against
the actual definitions, but the Lean patch has NOT been compiled here. No Lean
or Rocq compiler is installed in the searched PATH/standard local toolchain
locations. It must be compiled against the pinned project before adoption.

## Quantified effect

An independent, newly written data parser confirms that every one of the 2,240
Lean backward records is exactly `(b,a,−z,j,k)` of its forward counterpart. All
2,240 offsets are zero. The forward records also match all 2,240 Rocq records
exactly after decoding Lean's sentinel-bit pointer representation.

The reverse Lean data occupies 197,044 bytes in the materialized source; the
sixteen backward-check modules become unnecessary. These modules consumed
1,118.74 seconds in the published successful build record, out of 4,485.41
summed per-dependency compiler seconds for its 204 modules: 24.94% of that
recorded workload. This is neither a new benchmark nor an elapsed wall-time
claim, and the generic proof has an unmeasured cost. It is a concrete removable
workload, not a promised 25% end-to-end speedup.

Published successful build totals by component:

- Forward source checks, 16 modules: 1,087.66 seconds.
- Backward source checks, 16 modules: 1,118.74 seconds.
- Decoder site checks and assembly, 10 modules: 1,701.23 seconds.
- Bootstrap and assembly, 14 modules: 111.37 seconds.

The 95,714-step bootstrap is not the first optimization target: it accounts for
only about 2.5% of these compiler times.

## Second-stage cleanup: ordinary bisimulation

All offsets are zero, so the four-field ordinary RMBisim checker can replace
the offset checker after generalizing its pointer decoder. The existing ordinary
decoder uses128 fuel;622 pairs require more, up to176 bits. Use exactly the
512-fuel decoder of the offset checker, not the old128-fuel decoder.
`ZERO_OFFSET_STAGE.md` specifies the guarded translation and its proof obligations.
This removes irrelevant Int/offset machinery, but its further timing benefit is
unmeasured and likely less important than eliminating the backward checks.

## Rocq: same duplication, plus a concrete data compression

`Source215.v` runs `vm_compute; reflexivity` twice, first on `Cert215` and then
on `omirror Cert215`, and passes both facts to `ocheck_iff`. Unlike Lean, it does
not duplicate the reverse certificate in source. Prove once that checking the
forward certificate implies the mirrored check, or introduce the same semantic
bisimulation abstraction as Lean and prove its symmetry. Either route removes
the second full check without changing source/target programs or assumptions.

`Cert215Compact.v` is an additional, independently reconstructed representation
of the *same* certificate: two positive integers encode the paths, retaining a
leading sentinel bit. Its decoder restores every leading/trailing zero and all
2,240 rows exactly. All paths are at most 176 bits. The ordinary source drops
from 1,499,170 upstream bytes to 190,411 proposed bytes (87.3% smaller). The saved upstream certificate now has the exact upstream byte count; an
extra newline introduced by materialization was removed.

This compact representation uses standard positive constructors and a simple
structural decoder. It keeps the original Boolean checker and soundness
obligations. It is a data-compression prototype, NOT a proved runtime speedup,
and has not been compiled by Rocq. Before use, prove equality to the original
certificate or rebuild the unchanged endpoint with the decoded certificate and
run recursive coqchk. Keep the original checker, not an unchecked Python result,
in the logical trust chain.

## Next bottleneck: share decoder proofs with the correct context

The remaining largest cost is `KSites215`: 4,751 leaf occurrences checked in 105
blocks. `KSim.checkEdge` runs symbolic execution from the complete pointer Q,
with start tape `Q ++ zeros ++ header ++ box`. It checks the appropriate full
successor pointer (`incPath`, `breakPath`, or `continuePath`) and overflow flag.
`BoxLemmas` already shares arbitrary-register runtime proofs. Reproving those
lemmas per occurrence is not the current architecture and should not be proposed
as if it were a missing abstraction.

The next real improvement is a proof DAG for shared decoder scans and return
paths, separating:

1. Dispatcher traversal to a primitive entry, preserving an abstract untouched
   pointer prefix.
2. The existing generic register-box contract.
3. Pointer update/return, with a parameterized context and overflow condition.

The memoization key must retain the physical entry state, pointer context needed
by CB/CC (including the relevant enclosing branch boundaries), branch polarity,
marker/predecessor invariant, and expected exit contract. Identical source DAG
nodes alone are NOT an adequate key: continuation and break instructions depend
on their occurrence's ancestors, and contextual decoder aliases are real.
One cannot honestly replace 4,751 checks by 202 checks just by observing 202
source subtrees (the Lean path DAG itself has 179 internal nodes).

An incremental lower-risk experiment is to memoize certified symbolic trace
prefixes across the existing checks. Prove composition, instantiate the shared
trace lemma, and retain the existing full leaf coverage theorem. No requirement
to redesign the machine, source language or set-theoretic calibration follows.
Actual class counts and speedup must be measured after a context-aware prototype.

## Preserve the endpoint and its trust boundary

The exact certified baseline is candidate-k215/k215.tm, dense working states
0–214 and halt 215; its SHA-256 is
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
The Lean endpoint is `KEndpoint215.blank_halts_iff_zfc_refutation`, stating
`BlankHalts machine215 ↔ BProv ZFCax_s [] Form.fBot`. The Rocq endpoint is
`K215F.CorrectDense215.tm215_halts_iff_ZFC_inconsistent`, stating dense halting iff
`StandardZFC ⊢TC ⊥`. They are external correctness results, not unconditional
nonhalting and not an internal-PA independence endpoint.

Raw published Lean compiler logs list only `propext`, `Classical.choice`, and
`Quot.sound` for both endpoints. The two Rocq endpoint modules print four
`Closed under the global context` reports in total. The saved-record review
reports 237 selected modules and recursive coqchk exit code zero. These are
inspected published records, not an independently repeated build here.

Lean's existing `decide +kernel` checks should remain kernel-checked; replacing
them with `native_decide` would not be an equivalent trust-boundary change.
Rocq's `vm_compute; reflexivity` and the recorded recursive coqchk are distinct
from simply running a native Python simulator. Neither the data audit here nor
the original ordinary quantified-runtime scripts substitute for formal proof.

## Integration acceptance test

1. Compile the generic symmetry module and print its axioms.
2. Rebuild the shortened source instance and all dependent exact K215 endpoint
   clients from fresh objects, preserving endpoint statements.
3. Compare endpoint axiom reports to the published baseline.
4. For Rocq, compile and recursively coqchk the unchanged dense endpoint.
5. Record fresh source bytes, object bytes, per-module compiler times and peak
   memory. Do not infer gains from smaller source alone.
6. Only then remove old backward-check files and update generators so they stop
   emitting mirrored certificates. No repository files were changed or pushed.

## Reproducible local artifacts

- `audit_compression.py`: new independent parser/generator; does not import or
  execute downloaded repository scripts.
- `METRICS.json`: exact data checks and historical timing sums.
- `OffsetBisimSymmetry.lean` and `proposed/`: uncompiled Lean refactoring.
- `Cert215Compact.v`: uncompiled compact Rocq data, exact Python round-trip.
- `upstream/`: pinned source excerpts and raw proof-assumption/build records.

Primary source base:
https://github.com/VladimirReshetnikov/ProveIt/tree/c9dc79323429112c698100f3226a6e4d56c8b782/Computability/BusyBeaver
