# Independent mathematical and artifact review summary

Review scope: the new signed fourteen/sixteen-variable reductions, positive halved-carrier and shifted-scale norms, the signed24 weight, the source31/quartic50 register elimination, and the new nine-variable root majorants. This is an ordinary mathematical review supplemented by literal finite checks. It is not external human review, proof of consistency, an exhaustive audit of every inherited theorem, or a new kernel certificate.

## Results

1. **Signed14/15/16:** Pass. The final `signed/SIGNED_PROOF.md`, `build_signed.py`, coefficient recipe, and actual generated variable/guard interfaces were reread. Cofinal base selection, exact chosen-base propagation, odd-exponent square omega, signed weights, joint nonzero enforcement, and Pell-orbit j restoration are all accounted for. See `SIGNED14_15_INDEPENDENT_REVIEW.md` and `SIGNED16_INDEPENDENT_REVIEW.md`.
2. **Positive norms:** Pass. The halved carrier needs the new one-sided conjugate exclusion, not the old symmetric separator. The additional w shift is justified by a genuine source completeness property. The degree1061 proof must keep the tied −E0² eta term; the corrected nonzero leader is recorded in `POSITIVE_AND_INTEGER_NORM_REVIEW.md`.
3. **Signed24:** Pass. Dropping iI from the ratio weight follows from (Rac−1)iI>2 before any excluded-root positivity is assumed. The source1920/1936 leading certificate remains unchanged.
4. **Quartic31 and integer50:** Pass. The packing identity eliminates G using the retained N equation. In the positive31 family, the reverse map reconstructs positive G using transport. In the integer50 family, G is an unrestricted retained source register, so polynomial restoration alone suffices. The shifted positive transport coordinate is retained consistently. The tau^4 coefficient stays1, so the SOS degree is exactly4.
5. **Nine-variable majorants:** Pass at the inequality level. The parent separately audits the exact degree and code-to-proof correspondence. The majorant reasoning below does not depend on successful square recovery.
6. **Literal artifact structure:** Pass. `check_literal_structure.py` imports no builders and confirms the actual exported variable sets, gate counts, topological well-formedness, and full liveness for the nine principal outputs. Results are in `LITERAL_STRUCTURE_CHECKS.json`.

## Nine-variable majorant details

Use the source natural-domain facts sigma=Y(U+1)>0, |A|>=2, AE>=0, and D,F>=1. Let r=bw+phi, s=r+1, C=2R+s, H=(j+1)C−r. Then

    2RC+s^2=4R^2+2Rs+s^2>=0,
    2CH+r^2=2(j+1)C^2−2rC+r^2>=0.

Consequently MD=AC+sigma s^2+1>=|AC|+1>=sqrt(D), and CHbar=CH+r^2>=|CH|. The first identity uses A=R sigma. Also MF=AE+1>=sqrt(F).

For G1=A+F(CD+1−A),

    G1 H=FDCH+FH−A(F−1)H.

Thus |G1H|+|H|+1 is at most

    FD CHbar+(F+1)|H|+(F−1)|AH|+1.

For integer H, H^2>=|H|, and 2|AH|<=A^2+H^2. These give

    (F+1)|H|+(F−1)|AH| <= 2F H^2+(F−1)A^2.

Therefore the proposed MI=F(D CHbar+2H^2+A^2)−A^2+1 dominates |G1H|+|H|+1 and hence sqrt(|I|). Multiplying nonnegative majorants and adding1 yields V1=MD MF MI+1>sqrt(|DFI|). This covers C=0, E=0, H=0 and negative packed rank R. The finalizer's denominator/nonvanishing and domain obligations remain inherited and must not be replaced by an unrestricted-integer reading of the nine-variable equation.

## Important source-boundary corrections

- Source27's claim of the “same paper18 polynomial” must be read as a template identity before fixed rebinding. With its new tuple, it is a different fixed-coefficient polynomial.
- Do not infer a missing universal compiler adapter merely from source27's nine note delegating that dependency. Its `coefficients/COEFFICIENT_PROOF.md`, Sections6–7, explicitly argues the whole inputless interface, including ordinary quartic32 and the canonical signed restrictions. Its proof still depends on the named inherited compiler theorems and is not established by residue tests alone.
- The missing Wade notice in the original source27 delivery is a genuine packaging omission. By contrast, files removed by repository intake and ignored checksum ledgers do not prove a defect in the sealed delivered archives. Recovery/placement and original archive state must be distinguished.
- Keep the Jones parent witness parameter nu=31 distinct from the native coefficient exponent5^10 and from the output count9. Keep the entire coefficient tuple and all derived index leaves together.

Exact inspected sources are linked in the detailed review notes. Final numeric headlines should come from the sealed generated ledgers, since an operation-level improvement may occur after this prose was written.
