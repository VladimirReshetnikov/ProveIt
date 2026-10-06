# Complete guarded compiler with a shared integral quotient action

For r>=1 fixed relators, the complete positive7 polynomial now costs

    (303+40r+powcost(62+6r))M+(595+52r)A
      =898+92r+powcost(62+6r) operations,                 (1)

where powcost(t)=floor(log2 t)+popcount(t)-1. Its certificate is(280+40r+powcost(62+6r))M+(550+52r)A. It keeps23 comparisons,96+6r positive witnesses and the same ordinary x>0 interface. There are6+18r fixed roles. Compared with the [complete guarded parent](positive7_guarded_two_form_compiler_root.md), the exact saving is2r multiplications and2r additions; the prescribed exponent and its cost do not change.

This reduction preserves the entire polynomial, not only its ordinary-input projection, when both fixed coefficient interfaces come from the same actual relators. Consequently it preserves every supplied witness tuple and all positive zeros of the guarded parent. The numerical universal presentation and r remain unmaterialized, so(1) is a symbolic family count, not a numerical universal bound. For r=0 the exact903-operation,96-witness fallback remains. The general84 bound is unchanged.

## 1. The integral quotient identity

The [local quotient-pair proof](positive7_relator_quotient_pair_action_pascal.md) establishes the exact action cut. Write A=S(P) for an actual fixed relator P in SL2(Z), and V=[u;v] for the two integer right-basis rows already used by the guarded forms. They satisfy

    A-I3=E_plus*V, A^-1-I3=E_minus*V,
    V*C=[ell_1;ell_2].                                   (2)

For a noncentral relator, the primitive vector w obtained from(2q,p-t,-2s) is fixed by A and A^-1. The actual original-coordinate basis has u cross v=+/-w: in its preparatory coordinates the Bezout formula gives exactly -w, and undoing the permutation changes only this sign. Because w is primitive, choose a fixed integer row c with c*w=1. Then U=[u;v;c] has determinant+/-1 and an integral inverse. Its first two inverse columns J0 satisfy V*J0=I2, while its last column is w.

Thus I3=J0*V+w*c. Since A^-1 fixes w, the fixed integer matrix

    T=V*A^-1*J0                                          (3)

obeys V*A^-1=T*V. It is independent of the chosen integral section. Conjugating A^-1 by U gives last column(0,0,1), with T as the upper-left block; hence T has determinant1. Its trace is(p+t)^2-2, although no trace constraint is used to delete a runtime product here.

Now A^-1-I3=-(A-I3)A^-1 gives E_minus*V=-E_plus*T*V. Multiplying by J0 yields

    E_minus=-E_plus*T.                                  (4)

For P=+/-I2 the previous convention is V=[e1;e2], E_plus=E_minus=0. Use w=e3,c=e3^T,U=I3,J0=[e1,e2],T=I2. Equations(2)--(4) still hold, with no division by the vanishing original invariant.

All these choices and inversions prepare fixed integer numerals. No runtime witness, division or uncharged coefficient product is introduced. The new four `quotient_T` entries and six retained positive-sign `relator_E` entries per relator must follow this one recipe; the retained E entries are signed integers despite the sign-slot terminology. They are not arbitrary independent constants.

## 2. Exact paid splice on the original integer cut

The guarded source already computes, for each sign sigma,

    Q_sigma=hcenter*S_sigma,
    t_sigma,j=Z_sigma,j-Q_sigma, j=1,2.                  (5)

The two Q products and four subtractions cost2M4A per relator and remain paid. The old action appended E_plus*t_plus and E_minus*t_minus separately. For arbitrary integer pairs t_plus,t_minus and arbitrary existing(d,e,f) accumulators, replace their sum by

    E_plus*(t_plus-T*t_minus).                          (6)

Compute the four coefficient products in T*t_minus, its two row sums, and two differences with t_plus:4M4A. Then, for each of the three existing accumulators, compute its two E_plus products and add both into that accumulator:6M6A. This costs10M10A for the action, replacing12M12A. Including(5), the emitted replacement block costs12M14A=26 rows per relator, replacing14M16A=30 rows. Its unchanged two centered form producers still cost8M8A, so the full local producer/recovery/action total is20M22A.

For pair j the literal sign order is plus=8+2j, minus=plus+1. The new products are `quotient_T_j_a_b * signed_selected_form_minus_b`, followed by `signed_selected_form_plus_a - quotient_sum_j_a`. Only positive-sign E roles multiply those two differences. This direction is essential: T represents A^-1 on the quotient, and(4) supplies the minus sign in(6).

After a pair the three increment accumulators thread into the next pair. The first three paired increments are untouched. The final six increment ports replace the guarded parent's corresponding ports in the fused postprocessor. Zero, unit and negative coefficients remain literal charged products in the uniform source, including central relators. Syntactic liveness does not assert every contribution is nonzero.

## 3. Full polynomial and positive-domain preservation

All input, mass, selector, selected-output, guard, form, pack, prescribed-power, native and paired-action rows before the changed block are byte-for-byte identical to the matching guarded parent graph. Equation(4) proves(6) for every integer assignment at that block's input cut, independently of one-hot selectors, positive forms, guard satisfaction or history recovery. Induction over relator pairs preserves its final(d,e,f) increment values exactly.

The121-row suffix is then copied under only the six increment-name substitutions. It contains33 fused action rows,20 recurrence-right-side rows and68 finalizer rows. The finalizer is literally identical to the parent, as are all23 comparison endpoint pairs; all recurrences therefore retain their exact polynomial residual values. Under the fixed actual-relator correspondence, the whole output polynomial agrees for arbitrary signed runtime inputs. In particular, the ordinary input, complete supplied positive tuple and every auxiliary witness are unchanged.

The parent's guard-first native-domain proof, simultaneous state/form induction and positive completion therefore apply without a new existential map. The guard remains Cg*(DJ-S)=Ztot+g with its already corrected[joint_bound,joint_rhs] residual. This equality does not assert unconditional positivity of the computed forms: the earlier off-guard negative-form example and whole-pack79+D clarification remain valid. No native comparison, positive witness restriction or lane is deleted.

There are still8r signed form coefficients and six global roles. Twelve old signed action entries per relator are replaced by six E_plus and four T entries, giving6+18r roles in total. The common center, Cg, K and fixed positive7 lift use exactly the parent recipe; no new coefficient choice changes the guard's margins or height-selection argument.

## 4. Complete ledger and emitted evidence

| Disjoint stage | M | A |
|---|---:|---:|
| Input, mass, geometry, centers, guard and masks | 17+2r | 134+12r |
| Centered form producers | 8r | 8r |
| Three packs | 182+18r | 182+18r |
| Fixed prescribed power | powcost(62+6r) | 0 |
| Complete native certificate | 33 | 31 |
| Exact paired cut | 30 | 168 |
| Selected centers and quotient-pair appends | 12r | 14r |
| Fused positive lift | 12 | 21 |
| Seven recurrence right sides | 6 | 14 |
| Certificate | 280+40r+powcost(62+6r) | 550+52r |
| Residuals, squares and sum | 23 | 45 |

The old all-r grammar is changed only by the per-pair30-to26-row identity, so the displayed formula holds for every r>=1. No numerical extrapolation or assumption about monotonic power cost is used; ell=62+6r is unchanged. The ordinary input and the exact positive supplied list are copied, so their count remains96+6r.

| Saved full graph r | Polynomial M/A | Operations | Positive witnesses | Fixed roles |
|---:|---:|---:|---:|---:|
| 1 | 350 / 647 | 997 | 102 | 24 |
| 2 | 391 / 699 | 1090 | 108 | 42 |
| 4 | 472 / 803 | 1275 | 120 | 78 |

These three complete saved graphs contain3362 rows. The receipt has no additional formula-only samples. It binds each old cut range, old/new operation-label census, new compact cut digest, exact unchanged prefix, finalizer, comparison and positive-supplied-list equality, and final increment substitutions. It checks topological closure and syntactic liveness of every computed row and supplied port. A separate independent reviewer must authenticate those records and the fixed-recipe proof; structural self-checks alone are not a theorem audit.

## 5. Retained alternatives and open boundaries

**Review remark1 (rank alone does not supply the saving).** The local proof retains a valid two-sided plane factorization with generic cost13M11A=24, tying the old12M12A=24 action. It pays both2-by2 cores, their aggregation, sparse output reconstruction and all three appends. The present10M10A saving comes from the inverse identity(4), which makes one quotient action the identity. The tied schedule remains valid; neither is an optimality proof.

**Review remark2 (coefficient correlation and central cases).** Equation(4) is not valid for arbitrary independently assigned E_plus,E_minus,T. The actual-relator section recipe is part of the theorem. Likewise, dividing the raw right invariant by its gcd is not applied to central P=+/-I; the explicit identity-section convention handles that branch. Fixed zero/unit products stay paid, so no unproved sparse-support assumption is used.

**Open question3 (further quotient schedules).** Any smaller generic2-by2 action, favorable relator basis or special matrix family needs a separate integral fixed recipe and paid arithmetic schedule. Determinant1, rank and the displayed trace do not by themselves remove products or make a nonunit division free. Pascal is examining this continuation separately; no further saving is assigned here.

**Open question4 (numerical universal datum and source degree).** A concrete numerical universal presentation and its r, numerical matrices, numerical universal arithmetic bound, source degree and arithmetic optimality remain unproved in this lane. The local quotient proof's complete-composition question is resolved by this source only to the extent independently verified by its companion review. The unchanged group/native foundations retain their inherited scope.

The original metadata-only composer ran once and is now frozen with its first receipt. Receipt SHA256 iseda474bec49c4a2e4fef729c1cae8ed01ee940a8b63a56bb1e1d4cf64684f674; its sole input is the committed guarded receipt99e59b73bf1e6a9b0810f8ed862fefe62af00842edafd216e1c0420881ea7784. No supplied, archived, committed, predecessor or frozen code was run/imported; no saved source/coefficient arithmetic, degree propagation, scientific sampling, native witness testing or build was performed. The composer and all saved scientific artifacts must not be rerun or imported after freezing.
