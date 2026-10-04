# Independent review of the rational target-floor addendum

**PASS; no requested change.** The invariant-lattice argument, complete second-frame classification, group normalization and two-gate obstruction are sound in the stated model. The result concerns rational conjugacies preserving integrality of the entire inherited group and its group-wide first-row injectivity. It is not a lower bound for a predicate restricted to actual semigroup products, for arbitrary projections, or for a complete Diophantine representation.

## Reviewed pins

The complete author helper, receipt and note were read and authenticated:

| File | SHA256 |
|---|---|
| `matrix193_rational_target_floor.py` | `e7ebf6b107023bb2c01b786222179fc174e3289921a9308397f8f9d28cce9a02` |
| `matrix193_rational_target_floor.json` | `85b33bc0986d25eea3f2249abffdda1eba557b32ee50afcf658b6241f8e654a0` |
| `matrix193_rational_target_floor.md` | `ea7e7cd378f2b2ee8e01dfadafb8d936db1d2954efd989a53fe3e3c9626150ba` |

The full integral-floor companion and relevant Gamma1 group/encoding proof were also read as data. Their pins are respectively `ffbc7ec62eadaa323448b567722d1b8c0def4c5bd470eece020b53ed9bd42f30` and `6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742`. All five declared dependency hashes were independently authenticated. No predecessor helper was imported or executed.

## Proof challenge

An integral conjugate of a determinant-one group is equivalent to an invariant column lattice, with equality rather than merely containment because inverses belong to the group. Every full-rank rational lattice has the triangular basis used in the note: its horizontal intersection and vertical projection are cyclic, and a lift of the vertical generator can be reduced modulo the horizontal generator. After rational homothety, the basis is `[[1,q],[0,n]]`, with `0<=q<1` and `n>0` rational. This normalization does not assume the lattice was already rectangular.

The literal T and U conjugates impose integrality of n, 5/n, j=5q/n and jq. Thus n is 1 or 5. For n=5, integral j=q forces q=0. For n=1, j is an integer in [0,4], and jq=j²/5 integral forces j=0. These are all possibilities, without a bounded search premise. Conversely every matrix in the actual H has lower-left entry divisible by 5, so both resulting lattices are invariant under all of H. It follows that every admitted rational basis is a scalar times either I or diag(1,5), followed by an integral unimodular basis. No assertion that H equals the whole congruence group is needed.

The passage from H' to H is an integral unimodular change. The further conjugation by U leaves H unchanged because U belongs to H. Hence the two-lattice reduction applies to the actual inherited encoding and repeated block, rather than just to unrelated matrices with the same trace.

In the second frame, D5 is `[[0,15],[13,0]]`. For a zero-diagonal conjugate with positive lower-left entry c, the first column (p,r) satisfies `13p²-15r²=c*det(M)`, where c divides 195. I independently reconstructed all fourteen listed residue images from square residues; every exclusion and the two surviving signed values agree. These congruence exclusions apply to all integer p,r.

The surviving equations give exactly the stated families. Value 13 forces r=13h and `p²-195h²=1`; value -15 forces p=15h and `r²-195h²=1`. The forced second column therefore produces C or CJ, and a sign change gives the additional right factors E and JE. The elementary norm-one descent is complete: a positive unit greater than 1 has positive integral h and integral z>=14, making `14+sqrt(195)` the least such unit. Reduction by its powers proves the unrestricted signed-power classification. Since `14I+D5=-W5^-1`, every C acts by an inner conjugation of H5, even when C itself differs from a group element by -I.

Every surviving conjugated group contains a nonidentity lower unipotent: it comes from U5 without the interchange J and from T5 with J. Thus first-row injectivity fails on the entire group. This does not imply that the colliding matrices occur among products satisfying the directed lower-target condition; the author correctly makes no such inference.

Finally, integrality of the admitted group makes Dnew integral. Its off-diagonal entry v cannot vanish because 195 is not an integer square. For nonzero u, both outputs `(chi+28u*psi,28v*psi)` require gates. The first cannot be produced by one gate from the independent ports and integer constants. A two-gate circuit must therefore produce the second output first, then add or subtract it from chi, forcing u=±v. The resulting integral lower shear makes the diagonal zero and preserves first-row injectivity, contradicting the complete classification. Nonlinear intermediates cannot circumvent this two-output argument. The already injective original frame attains three gates, proving the claimed attained floor for this model.

## Replay and limits

Fresh normal and `python3 -O` exact author-receipt replays from `/` both passed on the frozen bytes. They cover 40 actual-generator integrality checks, 8,326 rational triangular examples, fourteen modular exclusion certificates, seventeen signed Pell examples, 68 explicit group collisions and sixteen lower-shear examples. The unrestricted lattice, Pell and gate arguments are the proofs above, not extrapolations from those finite examples. The independent additional computation reconstructed the fourteen residue images and authenticated the five dependencies; it did not invoke any historical builder.

Replay uses the author helper with `--root /absolute/path/native-stream-queue --expect /absolute/path/matrix193_rational_target_floor.json`, normally or with `python3 -O`.

The exact ordinary-input Pell index and unbounded membership certificate remain unpaid. Smaller product sets, changed alphabets, extra supplied coordinates, different projections and identities valid only on Pell points remain outside the floor. No repository or frozen source file was changed.
