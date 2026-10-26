# Reuse the last-slot finite equivalence for the terminal state

Pinned source: `22e020937caa81d0cb72a4f63071d6c0bcc1eba9`. This is an **uncompiled proposal**, with no runtime or kernel claim.

## Exact target and unchanged meaning

[WangMachineEncoding.stateNumber_injective, lines 34–51](https://github.com/VladimirReshetnikov/ProveIt/blob/22e020937caa81d0cb72a4f63071d6c0bcc1eba9/Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineEncoding.lean#L34-L51) proves injectivity by four cases on two optional states. The executable definition maps `none` to 215 and `some q` to `q.val`; it must remain unchanged.

Mathlib already supplies exactly the relevant equivalence:
`finSuccEquivLast : Fin (n+1) ≃ Option (Fin n)`. Its inverse sends `none` to `Fin.last n` and `some q` to `Fin.castSucc q`. Consequently the existing `stateNumber` is its inverse followed by `Fin.val`. Both maps are injective, so the target is composition of existing injection proofs.

Do **not** use the similarly named `finSuccEquiv`: its sentinel is the first slot, not the last, and it shifts ordinary states. The literal 215 terminal convention matters.

## Candidate proof

    have hcode : stateNumber = fun s : Option (Fin 215) =>
        ((finSuccEquivLast.symm s : Fin 216) : ℕ) := by
      funext s
      cases s <;> simp [stateNumber]
    rw [hcode]
    exact Fin.val_injective.comp finSuccEquivLast.symm.injective

The two-case pointwise comparison proves equality with the existing function; it does not introduce a new executable state encoder. No definition, theorem statement, bound, decoder calibration, target<216 guard or halted behavior changes. The six-line proof replaces the original 17-line body. Counting the declaration header gives 18→7 nonblank lines. The proposed standalone source patch also adds one narrow import, so that overhead must not be hidden in a whole-file savings claim.

The required pinned Mathlib API is [Logic/Equiv/Fin/Basic.lean, lines 186–204](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Logic/Equiv/Fin/Basic.lean#L186-L204). Its complete source and license are supplied under `evidence/`, with independently matched Git blob hashes and SHA-256. `Fin.val_injective` is already used in the pinned project's `Lean/checks/SplitSourceCarry.lean:9`. These source checks are not an elaboration test.

## Increment beyond the assumed applied baseline

The prior inverse-product graph proposal concerns missing coordinates of natural pairing witnesses. The finite-injective invariant proposal assumes an injective encoding to reflect dynamical invariants. Neither constructs the new machine's terminal-slot injection via the existing Option–Fin equivalence. After all prior proposals are treated as applied, the two-state case split in this newly added module remains; this candidate removes that residual proof work.

The separate machine-action proposal may consume `stateNumber_injective`, but it can do so using either the original or this replacement. The two edits affect distinct theorem bodies; neither requires the other, and no savings are counted twice.

## Adoption gate and artifacts

- `StateNumberCandidate.lean`: isolated candidate, explicit sentinel regression statements and axiom audit.
- `StateNumber.patch`: proof replacement plus the narrow Mathlib import, unapplied to the supplied snapshot.
- `WangMachineEncodingCandidate.lean`: complete proposed module for inspection; it is not independently compiled.
- `build_candidate.py`, `metrics.json`: deterministic textual reproduction.

Compile the proposed module and its Checks file in the pinned full checkout, inspect the endpoint axiom output, then replay the Action/Step/row-construction consumers. If the new import increases elaboration cost or obscures the small direct argument, retain the original. The justified benefit here is simpler reuse of a standard equivalence, not an asserted speedup.
