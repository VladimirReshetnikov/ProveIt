# Fixed-horizon quartic witness bit bound

Standalone companion research only; no report number is assigned and no file in
the existing compiler packet is modified.

## Result

For each fixed validated source s and n, the unique complete auxiliary natural
witness on an accepted canonical endpoint fiber satisfies

    max auxiliary <= C(s,n)(A+T+1)

when the initial coordinate magnitudes are <=A. The explicit finite computable
constant is C=(4B3+1)(alpha+beta), with the finite source/n formulas for alpha
and beta in `PROOF.md`, Section 5. Section 6 gives an independent executable
operation-majorant recurrence and a second valid constant.

Using the exact count W(T)=4max(n-1,0)+T(w_E+w_P), the sum of binary witness
coordinate lengths is O_{s,n}((T+1)log(A+T+2)). The proof covers target-domain
checks, inactive/rejected scratch, both directions, n<2 and T=0. It makes no
lower-bound, Theta, asymptotic inversion, or fixed-arity unbounded-time claim.

## Files

- `PROOF.md`: all-source structural proof and complete source-level gate audit
- `audit_bounds.py`: read-only operation-stream majorant calculator and tests
- `audit-receipt.json`, `audit-receipt-optimized.json`: exact computed constants,
  source hashes, witness counts, and validation details
- `audit.log`, `audit-optimized.log`: run transcripts
- `independent-review.md`: independent mathematical review
- `check_portability.py`, `portability-receipt.json`: absolute-prefix byte scan
- `plumbing-receipt.json`: required-argument and external-output rejection tests

## Replay

Both paths must be supplied explicitly. Run from this directory, with PACKET
pointing to the relocated source compiler packet and OUT to a pre-existing
external output directory:

    python -B audit_bounds.py --packet "$PACKET" --output "$OUT/audit-receipt.json" --include-cascade
    python -B -O audit_bounds.py --packet "$PACKET" --output "$OUT/audit-receipt-optimized.json" --include-cascade
    python -B check_portability.py --bundle . --output "$OUT/portability-receipt.json"

The audit rejects output paths inside either the input packet or this companion
folder. It reads the source packet without editing it, and imports disable
bytecode writes. Finalized externally generated receipts can subsequently be
copied into a new deliverable by the packager; replay does not overwrite the
bundled reference receipts.

Receipts identify the input by a stable reference label and its actual content
hashes, never its absolute runtime location. All consulted source/fixture hashes
are checked before and after the run. The portability checker scans all bundle
file bytes for absolute internal prefixes associated with workspace, root,
home-agent and opt-codex locations. It also requires an external output path.

The mathematical audit refuses any operation monomial containing two
coordinate-dependent factors; generic signed quadratic assignments are not
assumed to have linear height. These plumbing rules do not change its
mathematical tests or source binding.

Each run passed 66 one-block circuits, 332 complete block assignments and 72
accepted endpoint assignments. The receipts are identical after removing the
single `optimized_python` flag. These finite tests corroborate the structural
proof; they do not replace its all-source induction.

The bounds are deliberately conservative. The supplementary recurrence gives
an increment-right n=5 H with 1,146 binary digits; the explicit affine majorant
is much smaller. No small-constant claim for arbitrary sources is intended.

A zero raw-slot count need not mean zero scratch: for n>=2, `raw` allocates a
pair-gap register before any family loop. The theorem uses actual emitted
witness counts rather than discarding zero-slot blocks.
