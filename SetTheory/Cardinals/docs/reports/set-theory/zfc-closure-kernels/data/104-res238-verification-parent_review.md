# Parent mathematical and literal review

Reviewed 19 October 2026. Exact canonical table SHA-256:
909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08.

## Independent literal check

`independent_blank238.py` reparses the canonical file without importing either predecessor's interpreter. It checks exactly two rows at each working state 0 through 237, symbols 0/1, moves L/R, and one separate target-only halt 238. Two freshly written representations (sparse set and dense array with indexed transition arrays) agree on the entire initialized tape, head -5 and dispatcher 84 after 409835 transitions. The 351 one-cell positions equal the independently audited predecessor frame; every other cell is zero. This is an exact finite startup proof, not a nonhalting experiment.

## Review of the universal inference rules

The inherited symbolic checker was read in full through its transition, one-block induction and source-case functions. Its tape representation consists of finite affine-length homogeneous runs, an arbitrary finite tail of unary register blocks, and two infinite zero exteriors. Coefficients must be nonnegative before normalizing a run. A non-self-loop literal transition may expose a bit only when its affine constant is at least one. Therefore it does not assume an unknown natural is positive.

A homogeneous self-loop is accelerated by induction on its entire nonnegative length. For the opaque spare tail, each admitted traversal is first proved for one block with arbitrary natural value and arbitrary opaque exterior contexts on the actual supplied table. The four one-block identities take exactly v+2 transitions and preserve their boundary state and direction. Structural induction then permits traversal of any finite list, including the empty remaining tail. The mandatory first spare is represented separately, so the full spare suffix is nonempty.

The free-word normalization C(A)1 = 1B(A), with B(v)=0 1^(v+1) and C(v)=1 0 1^v, follows by empty-list and cons induction; its reversed identity is equally valid. It does not change the tape or head. Exterior zero absorption is valid only at an infinite blank exterior.

Every accepted nonhalting source case compares the complete final frame, register effect, spare suffix, state and exact head displacement with its specified successor. Halt cases must reach the unique halt state. Durations have 13 affine coefficients, all nonnegative; all 8386 accepted cases have positive constant at least 13. Maximum symbolic proof construction length is 463, below the 4000 proof-search cap. The cap does not bound register values or literal runtime. All 476 literal rows occur in the combined proof receipts.

## Composition and calibration

The frame uses an arbitrary additional natural gap beyond 64. Source paths have maximum length 48. Source instructions preserve or increase the gap parameter and do not remove the mandatory first spare. The separate source auditor checks zero-extension normalization of every nonhalting successor and the empty initial pointer. Consequently successive whole-frame contracts compose indefinitely, and positive finite durations exclude a spurious zero-time simulation.

The exact source transformations must be justified by control-flow equivalence, not just equality of leaf order. That independent audit checks all 13 stages and 25 rotations, every ordered instruction and every guarded successor. It identifies the starting source with the pinned SourceRotation240 program and the exact LogicalSeed246 seed. The local delayed-erasure route additionally has a freshly checked reachable-state guard; the direct whole-frame proof does not depend on that route.

The upstream BinaryRotation240 and CalibratedRotation240 sources at ce192939372ac7944fe2a0208c68a96d49fb5e3b were read and saved in `upstream/`. Their stated endpoints have no remaining runtime/coverage/startup premises and identify the calibrated source with conventional ZFC refutation. They were not freshly compiled here. The new argument composes the independently verified source correspondence, exact blank startup and universal binary execution contracts with the inherited mathematical calibration. All new proof ingredients are finite checks or elementary induction formalizable in ZFC. No assumption Con(ZFC) is used to prove the biconditional. Actual nonhalting follows under Con(ZFC).

This review does not claim a freshly compiled Lean/Rocq theorem or an internal PA proof for the 238-state table. It does not claim global state minimality or two-sided independence from mere consistency.
