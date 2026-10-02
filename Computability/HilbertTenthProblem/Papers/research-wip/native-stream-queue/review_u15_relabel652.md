# Independent review of U15 state relabel652

PASS on repaired source `cd3904fb083d1a254461ffde87636a6b9014bcdecb1db48cfcf2f30f41493879` and pinned parent `ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318`. Reviewed the complete Python, both emitted packets, full companion proof, and the parent proof/core construction previously reviewed separately. The independent executable and receipt are [review_u15_relabel652.py](review_u15_relabel652.py) and [receipt](review_u15_relabel652.json).

## Mathematical result

The permutation exchanges original state codes1 and9, fixes0, and retains exactly the original29 rules and edge-index coordinates. The guarded AST change replaces the sole terminal multiplication9P by1P, which the existing builder simplifies. Copies of the actual raw and ordinary builders regenerate the entire arithmetic source. The ordinary loader, program numerals, bit orientation, native witness coordinates and comparison ordering are unchanged.

Before either state equation is used, the common positive-domain geometry/bound/head/native comparisons recover P=B^t with B>=64 and the same one-hot chronological rule-index word. In the original state equation the constant, interior and terminal coefficients respectively enforce the initial code0, successive target/source equality, and final code9. All local differences have magnitude at most14<B. Replacing every code by the permutation and final code9 by1 gives exactly the same conditions because the permutation is injective and fixes0. This proves both directions on the same supplied positive witnesses, including the complete native witnesses. Raw tape parameters retain their natural domain. The result is stronger than language equivalence on valid programs, but it is not a claim about unrestricted signed zero sets.

Every other comparison is the same polynomial, proved by independent exact expression-DAG interning. The exact affine changes are

    Q_new-Q_old = 8(E2+E3-E18),
    N_new-N_old = 8(E0+E23-E17),
    E_i = edge_i-1.

Writing R=BN_old-Q_old-9P and Delta=B(N_new-N_old)-(Q_new-Q_old)+8P, the new residual is R+Delta. Thus the whole output difference, including every finalizer term, is exactly Delta*(2R+Delta) over all integers. This follows formally from the unchanged residuals, not merely the finite numerical evaluations.

The complete ledgers409=146M+263A and652=254M+398A save exactly one multiplication from410/653. Comparisons,105 ordinary positive witnesses, four program parameters, ordinary-input convention and conservative degree bound1936 remain unchanged. No87 improvement, exact-degree or permutation-optimality claim is made.

## Boundary defect found and repaired

The first draft reused preexisting sibling modules from `sys.modules`. A foreign `u15_raw_half_tape_loader` stub could return the real loader descriptor with `raw_Q_term` changed from `program_A*Q` to `program_B*Q`; the compiler accepted that arithmetic despite matching the parent source hash. Both reproduced cases are retained in the portable independent checker.

The repaired parent-import context temporarily removes every sibling module name and its temporary parent name, imports the pinned source with the intended sibling path first, then restores the caller's exact original module objects and path. Independent cold-cache regressions now pass for both a stub lacking `__file__` and a stub claiming a different project root. Both emitted arithmetic packets are unchanged by this import repair.

The external API uses explicit exact-type checks for packet mode, recursive canonical packet equality and coordinate validation. Parent source bytes are checked before each public access; the private cache is not exposed through build or polynomial_source. AST assertion checks and research verification require ordinary Python execution, as documented. Low-level research helpers are not treated as hostile-input public services.

## Independent evidence and limits

The focused replay passed:

- 61 unchanged exact residual-expression comparisons and58 transformed rule rows across both interfaces;
- 96 complete output corrections, including48 signed cases, and3,024 individual residual comparisons;
- 397 malformed input, option, packet/schema and changed-parent rejections;
- four defensive-copy checks and two cold poisoned-loader isolation checks.

The complete author's read-only receipt replay was also run independently on this source. The note's16 outer/AND fixtures are correctly described as using positive native placeholders. This review does not claim to have materialized complete Pell witnesses; the full positive extension is inherited unchanged from the reviewed parent theorem. No additional primary-source reinterpretation is needed, since the literal tape machine, program recipe and input orientation are unchanged.

No remaining mathematical, source-transfer, scope or tested public-boundary finding.
