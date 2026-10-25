# Direct quartic construction component

The final selected family uses the **odd affine radix q=2z+1**, the
**original beta base y=V(V-1)**, the new shared bootstrap norm, and the
inherited deterministic Pell comparison center. It preserves the entire
fourteen-pair squared orientation pool. The full new semantic proof is
written in the enclosing research report; finite transformations and
coefficient files are supplied here.

## Recommended data

- `candidate244/`:244 variables,181 rows,5346 terms,height128446; full raw
  source, new source delta, monic projection certificate and translations.
- `equation240/`:240 variables,177 rows,21482 terms,height6144.
- `equation241_affine_balanced/`:241 variables,178 rows,5351 terms,height15107.
- `equation241_affine/`:241 variables,178 rows,9544 terms,height4512.

All are ordinary degree-four integer-coefficient polynomials over all
integers. Each is exactly the sum of squares of the finite residual list
in `equation.json`; `expanded_polynomial.json` lists all collected
coefficients. Variables and monomial indices are zero-based. A sparse
term `[c,[i,j,...]]` means c*x_i*x_j*..., and an empty index list means
the constant term. Intermediate source coordinates are actual quantified
coordinates before the explicitly certified projections, not hidden
function symbols.

`parent252/` is an unchanged copy of the matched current252-variable
common-remainder source, including its finite reconstruction and retained
ordinary proof/calibration closure. Its complete independent verifier and
19-file byte-for-byte rebuild were replayed successfully; the receipt is
`PARENT252_REPLAY.json`. Inherited licenses and notices remain in that tree.

## Reproduction

Standard-library Python3.10 or later suffices. No network, solver, machine
simulation or proof search is used by the exact checkers.

    python3 verify_unified_bootstrap.py --affine-radix
    python3 -O verify_unified_bootstrap.py --affine-radix
    python3 verify_affine.py --profile equation240
    python3 -O verify_affine.py --profile equation240
    python3 verify_affine.py --profile equation241_affine_balanced
    python3 verify_affine.py --profile equation241_affine

Actual normal/optimized receipts are the `VERIFY*.json` files. Read-only
checkers reconstruct complete mathematical identities; they do not alter
the emitted equations. The new source checker has9 negative controls; the
affine/row checker has7. None uses Python `assert` for required validation.

To regenerate the core from the unchanged parent:

    python3 build249.py
    python3 build_unified_bootstrap.py --affine-radix
    python3 build_affine.py --affine-radix
    python3 build_affine.py --affine-radix --dense

These commands emit the raw affine-exposure stages. `reduce_rows.py` is
the bounded deterministic discovery routine for the final integer row
certificates; replaying its search is not necessary to check the result.
`verify_affine.py` replays the entire frozen certificate and independently
recomputes the full output exactly. `select_balanced.py` selects the stated
prefix from that frozen sequence, not an unrestricted optimum.

## Earlier comparison stages

The250/249 stages compose already-delivered odd-square and center lemmas.
The245/246 stages use the new shared bootstrap norm with an odd **square**
radix and the larger beta base y=V(V-1)+(B-1)^2. They are distinct
polynomials with separate proofs, not alternate presentations of the final
odd-affine-radix construction. `PROOF.md` and `PROOF249.md` document the
earlier compatible composition. `candidate241` and `equation241` without
the `_affine` qualifier descend from that earlier squared-radix branch.
They are retained as transparent research checkpoints and should not be
mixed with the final branch's source meaning.

`ODD_SQUARE_SOURCE_PROOF.md`, `DETERMINISTIC_CENTER_SOURCE_PROOF.md`,
and `AFFINE_EXPOSURE_SOURCE_PROOF.md` are attributed copies from the
current inspected incoming archives. `AFFINE_COMPOSITION.md` describes
their exact finite use here. The new shared-bootstrap and signed-radix
arguments are in the enclosing main report. No global simplicity minimum,
consistency decision, or new end-to-end Lean/Rocq formalization is claimed.
