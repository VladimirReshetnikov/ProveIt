# Natural quartics from pooled self-radix digit budgets

This component gives four literal equations over **nonnegative integers**. Their lack of zeros is equivalent, by ordinary mathematics formalizable in ZFC and the retained C222/refutation calibration, to Con(ZFC). It does not prove consistency or claim a new end-to-end proof-assistant endpoint.

| Profile | Variables | Quadratic residuals | Collected quartic terms | Height |
|---|---:|---:|---:|---:|
| natural221 | 221 | 171 | 13,935 | 118,464,197 |
| natural222, balanced | 222 | 172 | 9,917 | 83,954,634 |
| natural223 | 223 | 173 | 7,202 | 83,954,472 |
| natural224_sparse | 224 | 174 | 6,527 | 83,953,869 |

Each polynomial has exact degree four. In every profile, `natural/equation.json` defines the entire list of residuals R_i and the equation is sum_i R_i²=0. `natural/expanded_polynomial.json` lists every collected coefficient. A term `[c,[i,j,j]]` means c*z_i*z_j²; `[]` is the constant monomial and indices are zero-based. The ordered coordinate list is part of the equation. Every declared variable occurs. Natural and unrestricted-integer dimensions must not be compared as though their domains were identical.

The balanced222 profile improves the newly arrived natural226 construction in variables, residuals, support and height. The minimum221 profile trades greater support and height for one fewer variable; it is not globally optimal. The incoming226 values were independently recollected from all literal residuals and compared to every stored expanded coefficient. Its complete source verifier and unbounded theorem were not independently rerun/reproved by that metric check.

`PROOF.md` is the full new ordinary proof. Incoming graph_digits supplies the low-digit pooling idea; Round17 supplies the aligned self-sized radix and semantic anchor. Their composition and a weighted adjacent-denominator/absorbed-output refinement lead to these equations. `proofs/` retains the original parent theorem and its arithmetic dependencies; inherited calibration boundaries are expressly preserved.

## Reproduce

Python 3.10 or later, standard library only; no network, external source checkout, symbolic algebra package, or proof assistant is needed.

    python3 -B verify.py --rebuild
    python3 -B -O verify.py --rebuild

Verification is read-only, with reconstruction in a temporary directory. Optional `--output /outside/path/result.json` records a receipt. It checks the complete parent affine export, every changed and unchanged pooled row, all nonnegative projection certificates, the complete coefficient expansions, liveness and metrics, and 21 deliberate corruption cases. It recreates twenty selected mathematical artifacts byte for byte. The numerical checks supplement but do not replace the unbounded proof.

To construct all profiles at another location:

    python3 -B reproduce.py --output /empty/destination

The explicit row orders in `PROFILE_RECIPES.json` are part of each reproducible construction. The random search used to discover one order is unnecessary for replay and not claimed as an exhaustive optimization. `ENDPOINTS.json` is the machine-readable endpoint catalog. No repository publication is performed by these scripts.

## Reviewed executable boundary

The inherited `code/contract.py`, `code/check.py`, and `code/affine_check.py` were read in full before execution. They perform local exact integer/rational arithmetic only. The newly written `build.py`, `reproduce.py` and `verify.py` use them as documented; output writes are explicit or temporary. The delivered equations are not modified by verification. Separate-agent mathematical review in this workflow is not external human peer review.

A separately written named-coordinate transformation audit is available as `python3 -B review/check_natural_transform.py` (also `-O`). It checks all four raw transformations and rejects fifteen additional corrupted pooled rows. Its full mathematical review and original/portable receipts are in `review/`.
