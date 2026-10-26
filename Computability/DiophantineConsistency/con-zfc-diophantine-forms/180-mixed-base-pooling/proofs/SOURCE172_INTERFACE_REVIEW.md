# Independent review of the exact source-172 interface

This is an internal AI-assisted mathematical and finite-data review. It is
not an external referee report or a newly compiled Lean/Rocq theorem.

## Exact input and domain

The input is the pre-row-reduction `signed/stages/affine216/equation.json`
from source 172, Pooled Powers Round 21, at ProveIt commit
`ef0c534c1ae1e312c61a2a9a5a3f18f5516fd42b`. Its SHA-256 is
`e5e14bc0bbabb625f78ce57017fbdb336c4a65c5877f517142c399769992ff39`.
It has 216 unrestricted integer coordinates and 153 quadratic residuals.
The published row-reduced 216-variable sum of squares has the same zero set;
we use the earlier chart because the five power interfaces are still isolated.

The checker `code/audit_source_interface.py` expands the actual integer
polynomials and authenticates every statement below. No source constructor
or heuristic search is imported by that check.

## Complete deleted block

All indices here refer to the original 216-coordinate chart, before compact
renumbering. Delete exactly these ten rows and ten coordinates:

| Block | Deleted rows | Deleted coordinates |
|---|---|---|
| base t, output F, index t | 97, 98 | 140, 141 |
| base B, output N, index x | 99, 100 | 142, 143 |
| base BH, output q, index x | 101, 102 | 144, 145 |
| eleven requests at q+1 | 149, 150 | 212, 213 |
| three requests at q | 151, 152 | 214, 215 |

Every occurrence of a deleted coordinate is confined to a deleted row.
Every base, output, requested index, and Pell-coordinate expression is
independent of those coordinates. Therefore replacing these blocks leaves
the other 143 quadratic residuals literally unchanged.

The actual affine ports have the following essential offsets:

- `A = shared.A + 1`;
- `q = 4*radix.odd_square_root_half + 1`;
- every stored `index*.X_minus_AY` is the actual difference `D=X-A*Y`;
- actual `Y_3 = index3.Y - 1`;
- actual `Z_12 = mul.645 + 1`;
- all other listed ordinates and AY wires have no offset.

In each case the actual abscissa is `X=D+Z`. The derived index J is the
explicit affine expression obtained by the final monic projection of
`add.380`; it is recorded in the machine-readable interface. Treating J as
an extra variable or as a small decoded label would be incorrect.

## Exact retained Pell information

The interface contains fourteen principal pairs, indexed by
`0,2,3,5,6,7,8,9,10,11,12,13,14,15`.
For every pair, two retained rows are exactly, up to a recorded sign,

    Z - A*Y = 0,
    D^2 + 2*D*Z + Y^2 - 1 = 0.

The second equation is the Pell norm after the invertible change
`X=D+Z`, using the first equation. All twenty-eight rows are retained.

Retained row 129 is exactly

    W - 2 - sum(atom^2 for atom in the 34 actual atoms) = 0.

The finite auditor verifies all 34 squares and verifies that the actual
base, output, and requested index of each of the seventeen power requests
belongs to this list. The literal horizon row gives `t=16+h^2`, so
`W >= 258`. No positivity of B, BH, q, or a proposed output is presumed
in this square-frame identity.

Retained row 142 is exactly

    sum[(X_i-1)^2+(Y_i-k_i)^2] - (A-1)*Q
      - sum[X_i^2+Y_i^2-Z_i^2-1] = 0.

Thus the unchanged norms restore the parent's pooled orientation equation.
The cap, semantic-anchor assembly, odd frame, and horizon rows remain in
the retained body. The source's ordinary proof derives `|A|>W^W` and the
canonical signed pairs at their requested indices from this information
before interpreting any deleted power congruence. This ordering is stated
in source172 `PROOF.md`, sections 1 and 4, and developed in the retained
`ORIENTATION_FIRST_PROOF.md` and its signed-anchor predecessors. It is not
an inference from bounded numerical tests.

Consequently the mixed-pool theorem may use the source's signed-frame and
canonical-pair hypotheses without first proving that all bases are nonzero
or that the encoded arithmetic registers have their eventual positive signs.

## Exact old power identities and restoration

Write `T=2*A*n-n^2-1` and `e=m-D-n*Y`.
For the first three blocks the deleted rows are the modulus definition and
`e+T*Q=0`, up to a recorded row sign.

For either larger block let

    H = sum Y_i*(m_i-X_i),
    S = sum[(m_i-D_i)^2-Y_i^2],
    E = S - 2*n*H.

The old two rows are exactly

    K - 2*H - (2*A-n)*L = 0,
    S - n*K + L = 0.

Together they say `E=T*L`. The retained AY rows give the identity

    sum e_i^2 = E - T*sum Y_i^2.

This identity fixes which quotient is used: an E/T quotient differs from
the quotient of the full squared errors by the integer `sum Y_i^2`.
It is safe to use either only if the corresponding restoration formula
is changed consistently.

Once the new theorem restores each individual old power congruence, set
the singleton quotient to `-e/T`. In a larger block set `L=E/T` and
`K=2*H+(2*A-n)*L`. Every omitted row is then restored exactly.
If n=0, `T=-1`, and these divisions are automatically integral. Thus a
zero base requires no new bootstrap convention: the old blocks at that
base can still be restored, and the full parent's soundness argument
applies afterward. In the forward direction, each old block already has
integral E/T, so any declared sum of these quotients has an integer witness.

## Arithmetic and logical ancestry

The arithmetic ancestor is the 239-coordinate Strict Horizons source
from source162, with the factorial-free CRT and numerical C222 calibration
retained below it. Source172 then performs private-wire aggregation,
fixed-base pooling, Pell difference shears, its explicitly proved odd beta
change and wider remainder sphere, four monic projections, two common
Hessian-direction projections, and one affine projection. The credited
source158 pooling module supplies a reusable theorem and checker; it does
not replace this arithmetic ancestry.

The retained logical interfaces are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.
The ordinary proof composes the explicit polynomial zero-set equivalence
with those C222/ZF/ZFC refutation calibrations. No assertion of consistency,
new encoded internal-ZFC proof string, or fresh end-to-end formal-assistant
build follows from the finite checks.

## Performed finite replay

The exact source172 `signed/` dependency tree was reconstructed from the
repository's recorded PLACEMENT byte-copy map. Four formal interface files
outside the sparse checkout were read at the same immutable commit. The
complete retained-path, original-path, byte-length and hash ledger is
`inherited/source172_PROVENANCE.json`; original notices remain with the
inherited files.

Both the new-stage-only source172 verifier and its full advertised source
replay passed. The latter includes the Strict Horizons literal edits,
all seventeen power interfaces, all 34 frame atoms, all fourteen pairs,
eighteen Horn factorization identities, 198 source monic projections,
source reconstruction, the earlier factorial-free and normalized-parent
replays, and whole quartic coefficient comparisons. Receipts are retained
as `inherited/source172_finite_replay.json` and
`inherited/source172_full_replay.json`. These are finite algebraic checks;
the cited ordinary arguments supply the unbounded semantics.
