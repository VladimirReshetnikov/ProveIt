# Independent intake and transport-pivot review

Reviewed repository: `c1a102936aca437e9999530a0111e6ddab56dc6d`.

## Intake scope and collision avoidance

All five current `docs/incoming/*.zip` files were read. Their immutable arrival hashes and sizes are in `audit_summary.json`. The four substantial packages were extracted and their README, main theorem declarations, relevant integer proof sections and literal interfaces examined. This review is not a replay of every delivered program or a reproof of all inherited Pell/native semantics.

The current incoming queue already contains the following unrestricted-integer points: 37 variables at degree 4, 30 at degree 6, 25 at degree 8, 24 at degree 10, 23 at degree 12, 22 at degree 14, 21 at degree 20, 20 at degree 32, and 19 at degree 88. A ten-integer high-degree equation is also present. None of those should be presented as a new result of the current iteration.

In particular, composing signed power recovery with determinant guards and deleting the `q(q-1)` denominator factor via adjacent-coefficient Pell descent have already been delivered. The eleven-positive degree-277/111-operation equation occurs in all four substantial incoming packets. A degree-257/114-operation companion occurs in Joint Guards. Descending coefficient budgets and commutative proof certificates have also been proposed, with explicit unfinished global closure.

The small `report.zip` contains only `report.tex`. Its missing `\input` files and the absent literal packets prevent calling its new nine-variable degree-1,158,240/811-operation or twelve-variable degree-70/100-operation equations independently reproduced deliverables from that ZIP. Its ordinary prose arguments can still be read and cited as manuscript claims.

## New composition found in this review

The late projection family in Joint Guards retains the transport equation

`(K0+W)*(q-F-alpha)-F-z*(q-1)=0`.

Structural Reductions already proves a monic transport pivot, but only applies it to earlier projection points. Combining it with the late family appears not to be present in any inspected authored incoming text.

Introduce the complementary coordinate `C=q-F-alpha`. Then the same row is

`(K0+W)*C-F-z*(q-1)=0`,

so set

`F=(K0+W)*C-z*(q-1)`,

`alpha=q-F-C`.

These are integer polynomials. No division, rational-root argument, sign inference, cofinal family or calibration change is needed. Projection sends an old zero to its value of `C` and forgets `F,alpha`; restoration recovers those two coordinates by the displayed formulas. The maps are inverses on zero sets, with all other coordinates unchanged. This is stronger than an existence-only canonical-witness argument.

Consequently the incoming (22,16), (21,20), (20,32), and (19,88) points yield (21,16), (20,20), (19,32), and (18,88), respectively. Their literal packets and exact-degree checks are supplied in the final integer component. The later two-root merger improves the integer family further to 17 variables at degrees 112 and 110; a midpoint/product companion gives 18 variables at degree 80. Those additional constructions have their own proofs and the independently implemented `independent_review.py` / `certificates/INDEPENDENT_REVIEW.json` there.

## Degree reasoning independent of a generator

After pivot, `F` has degree 2 and `alpha` degree at most 2. The coefficient mask polynomial admits the exact rewrite

`R=(q-F)*(q^3-q)-C*(q^2-1)+(MC+q*MF)*(3*J3+1)`.

Its degree is at most 5. The calibrated determinant

`det=(cone_A*F)*(cone_B*C)-(q-cone_A*F-cone_B*C)^2`

has degree at most 4. These are the only affected high-level inputs. In the two smallest-degree target systems this raises the joint guard residual to degree at most 8, already within the claimed bounds; in the larger-degree systems the existing `eta*(k-eta)` contribution remains dominant. None of the named power or coordinate registers is a new unknown.

The incoming exact-degree witnesses survive the substitution:

- (21,16): coefficient of `a^4*f^8*o^4` is 1. The squared auxiliary residual contributes it. The new guard cannot contribute because its dependence on `f` is too small; other rows also lack the required exponent.
- (20,20): coefficient of `f^4*v_scale^4*J3^12` is `2^4*3^12*beta^12`.
- (19,32): coefficient of `eta^4*h^4*w3^4*v_scale^4*J3^16` is `2^12*3^20*beta^16`.
- (18,88): coefficient of `h^8*w3^8*v_scale^16*J3^56` is `2^32*3^64*beta^56`.

All four numbers are nonzero on the authentic coefficient slice. The authored component supplies exact literal checks of the parent projections and row operations. This note records the separate ordinary mathematical degree reasoning, rather than claiming to duplicate every implementation check.

## Coefficient and semantic boundary

Joint Guards and Structural Reductions use byte-identical values of the same six constants, checked by independent gzip decompression and SHA256 comparison. They occupy 615,883 minimal raw bytes and 10,607 compressed bytes in the retained payload representation. Their binding is:

- `beta=2^1064921-1`;
- `K0,MC,MF` are the coherent `mixed-parity-unrounded-1064921` source34 tuple;
- `cone_A=2^1113`, `cone_B=2^666104`;
- `MF` is already shifted by `beta` and must not be shifted again.

No compact44 or compact54 coefficient substitution is licensed by this review. The monic pivot is uniform over all coefficient values, but the inherited native calibration and determinant completeness are for the named tuple.

The parent guard composition proves signed soundness for arbitrary zeros and completeness by regenerating canonical accepting witnesses. Its link to finite ZFC refutation uses the inherited signed/main/strong Pell classifications and index recovery, native canonical digit/phase/carry geometry, the full native source/tableau compiler and the fixed K215/refutation calibration. The current transformation introduces no additional such dependency.

The new algebraic equivalence is elementary and formalizable in ZFC (indeed its polynomial part is valid over every commutative ring, while sum-of-squares conjunction uses the ordered integer domain). A finite algebraic verification is not an end-to-end Lean/Rocq or object-language ZFC certificate. The repository's outstanding global native and internal nonstandard proof-code interpretation obligations remain separate. No assertion of Con(ZFC), no consistency assumption, no global simplicity optimum and no worldwide historical novelty claim follows from this review.

## Final iteration boundary

The final iteration also completes a ten-positive-variable four-root reduction of degree 1,152 in 131 live binary operations. Its separate `INDEPENDENT_MATHEMATICAL_REVIEW.md` reviews the unbounded arithmetic: unconditional exclusion of every signed subset cancellation, positivity before residue separation, the order of normalized and auxiliary Pell-index recovery, and the strict bound that restores the mixed main and transport residues. This result repairs the two explicitly unresolved four-root obligations in the incoming Joint Guards note; it does not merely repeat the previously delivered four-root suggestion. Its exact norm/degree/circuit verification is a separate component receipt.
