# An integer selector sphere reduces the bounded van Kampen compiler

The [guarded transfer](van_kampen_selector_sphere_projection.py) reduces the imported all-label area-budget compiler from

    (2s+13)m−4 integer witnesses and (2s+11)m residuals

to

    (2s+12)m−8 integer witnesses and 10m−4 residuals,

for s>=1 relators and external budget m>=1. Every residual remains quadratic and the final sum of squares has exact degree4. The m=0 source remains its four linear boundary residuals, no witnesses, and degree2. For one relator and one cell, the allocation drops from11 witnesses/13 residuals to **6 witnesses/6 residuals**.

The new and parent integer zero sets are in **bijection by explicit coordinate projection and reconstruction**, with all four boundary parameters unchanged. This is a statement about a fixed external budget. The witness tuple still grows with m; neither a fixed-arity universal equation nor an arithmetic-operation improvement is claimed. The [receipt](van_kampen_selector_sphere_projection.json) contains the complete parent and successor sparse residual sources for15 checked forms.

## 1. Frozen actual compiler and domain

The parent is `code/van_kampen.py` in the incoming `arithmetic_van_kampen.zip`, arrival `6914ccca6`. Its all-label compiler allocates a chart matrix U_i, an unrestricted product matrix V_i, q=2s+1 selector integers e_ij, and intermediate product matrices P_i. Its fixed endpoints are P_0=I and P_m=W. It emits, for each cell,

    E(U_i)=0,
    e_ij(e_ij−1)=0 for j=0,...,q−1,
    sum_j e_ij−1=0,
    V_i−P_(i−1)U_i=0,
    V_i C_i−P_i U_i=0,
    C_i=sum_j e_ij R_j, R_0=I.

A matrix residual contributes four scalar rows. All coordinates are integers, including the four chart coordinates; they are not natural or positive witness counts. The first chart matrix is

    U_1 = [[1+4u0_x, 2u0_y], [2u0_z, 1+4u0_t]],
    E(U_1)=u0_x+u0_t+4u0_x*u0_t−u0_y*u0_z.

The Python names use zero-based cell numbering, so mathematical V_1 is the four coordinates named `v0_*`.

The executable reads the ZIP in memory without extracting it. If the incoming file has been retired, it reads the identical archive using `git show 6914ccca6:docs/incoming/arithmetic_van_kampen.zip`. The whole archive must have SHA256

    c29f2918b5cddda37ca4a0190fbeba1930015c7d8e4a3fa55f13b5dd233e6ed9

and the inspected Python member must have SHA256

    976def6231c12f50ff9336a9c1bd604bf2fb6a96de4dffad4b29121c362625f3.

Only that member is loaded, under a temporary module registration that is restored afterward. It supplies the actual `compile_budget` output used in every transfer. No general archive script or verification entrypoint is executed by the loader.

## 2. One quadratic replaces the entire selector block

Keep only the nonidentity selector coordinates e_1,...,e_(q−1). Define

    T=sum_(j=1..q−1) e_j,
    S=sum_(j=1..q−1) e_j²+(T−1)²−1.                (1)

For integer selectors, S=0 means the displayed nonnegative squares sum to1. If all e_j=0, then T=0 and the final square is1. Otherwise exactly one e_j is±1 and every other e_j is0. The final square must then be0, forcing T=1 and the nonzero selector to be+1. Conversely each of these possibilities satisfies(1).

Thus the allowed choices are precisely the zero vector and the positive coordinate basis vectors. They encode the identity label and each nonidentity label, respectively. Restore

    e_0=1−T.                                       (2)

The complete old selector vector is now exactly one-hot. The selected matrix becomes

    C=I+sum_(j=1..q−1) e_j*(R_j−I),                (3)

which is the literal old selected expression after substitution(2). Repeated relators and freely trivial relators cause no difficulty: the coordinates still distinguish their label indices.

There is an exact alternative check against the actual old source. Write B_j=e_j(e_j−1), with e_0 restored by(2). Then

    S=sum_(j=0..q−1) B_j.                           (4)

Each B_j is nonnegative for every integer e_j. Therefore S=0 if and only if every old Boolean residual B_j vanishes. The old selector-sum residual becomes identically zero under(2). The implementation verifies(4) symbolically against each imported selector block, rather than substituting an independently constructed example.

Integrality is essential. At `(e_1,e_2)=(2/3,2/3)`, S=0 although the restored selectors are `(-1/3,2/3,2/3)`, whose Boolean residuals are nonzero. No rational or real zero-set bijection is asserted.

## 3. Remove the first product matrix

Because P_0=I, the actual first defining matrix equation is V_1−U_1=0. Substitute

    v0_00=1+4u0_x, v0_01=2u0_y,
    v0_10=2u0_z, v0_11=1+4u0_t.                   (5)

Remove those four variables and their four defining residuals. The first transition equation is now U_1 C_1−P_1 U_1=0. Both U_1 and C_1 are affine in the remaining coordinates, so every entry is still quadratic. For later cells the V_i matrices remain paid; their elimination would generally reintroduce a cubic product and is not part of this transfer.

Every retained parent residual is expanded after the actual substitutions(2),(5), serialized with exact integer coefficients and checked as an exact sparse polynomial identity. The output records a map from each new row to its corresponding old row or selector block, plus the old rows that become identically zero.

## 4. Complete integer-zero bijection and off-zero correction

Project an old zero by deleting e_i0 in every cell and the four `v0_*` coordinates. Its selector-sum and first-product equations force exactly(2),(5). Its Boolean rows imply S_i=0, and every retained mapped row vanishes, so the projected tuple is a new zero.

Conversely, start with a new integer zero and reconstruct(2),(5). The square-sum argument for S_i restores every old Boolean row. The old selector-sum and first-product rows vanish identically, and every other old row agrees with its retained mapped row. Thus the reconstructed tuple is an old zero. The two maps are inverse on these full zero sets, with no replacement of conjugators, boundary matrices or private native witnesses.

Off zero, the complete polynomials differ. Let F_old and F_new be the sums of squares of all respective residuals, and let L be reconstruction(2),(5). Equation(4) gives the exact identity

    F_new(v)−F_old(L(v))
      =sum_i [(sum_j B_ij)²−sum_j B_ij²]
      =2 sum_i sum_(j<k) B_ij B_ik.                (6)

All other residual contributions coincide, and the removed defining rows are zero after L. Formula(6) holds as a polynomial identity, including off zero. For integer inputs its right side is nonnegative. Neither the final polynomials nor arbitrary full parent tuples are identified unchanged.

## 5. Literal allocation and degree

Deleting one selector per cell and four first-product coordinates gives

    [(q+12)m−4]−m−4=(q+11)m−8=(2s+12)m−8.

The old q Boolean rows plus one selector-sum row are replaced by one sphere row, saving q rows per cell. Removing the four first-product rows then gives

    (q+10)m−qm−4=10m−4.

For m=0 no substitutions or allocations are made. The original four boundary residuals are preserved verbatim.

|Relators s|Budget m|Parent witnesses|New witnesses|Parent residuals|New residuals|Exact SOS degree|
|---:|---:|---:|---:|---:|---:|---:|
|1|0|0|0|4|4|2|
|1|1|11|6|13|6|4|
|1|2|26|20|26|16|4|
|1|4|56|48|52|36|4|
|2|1|13|8|15|6|4|
|3|1|15|10|17|6|4|

All transformed residuals have degree at most2. For m>=1 the retained chart equation has a nonzero homogeneous quadratic part, so the homogeneous degree4 part of the final SOS is a nonzero sum of real squares. This proves exact degree4, independent of whether some relators coincide or are trivial. The zero-budget linear boundary rows similarly give exact degree2. The receipt checks maximum residual degree directly from the emitted sparse monomials.

These are literal source counts and degree statements. Expanding or evaluating the selected matrices and sphere rows still costs arithmetic depending on s; no scalar straight-line schedule or operation optimum is claimed. Integer-to-natural conversion would add coordinates and requires its own stated comparison.

## 6. Public guards and executed checks

`build`, `canonical_parent` and `rewrite` require a nonempty list or tuple of relator strings over `aAbB` and an exact nonnegative integer budget. Boolean and float budgets are rejected. `rewrite` compares every supplied parent field to the complete canonical imported packet with recursive type-sensitive equality. Successor APIs likewise require the complete canonical successor, including its source, row map, eliminated coordinates, degree and scope metadata. Float or Boolean coefficient substitutions and list/tuple schema changes do not pass that comparison.

Every serialized polynomial coefficient must be an exact integer; Float atoms and nonintegral coefficients are rejected before conversion. Assignment APIs require precisely the complete named integer coordinate set, including at budget zero. `lift_assignment` and `project_assignment` expose the explicit maps; `evaluate` returns the integer SOS; `correction` checks(6) on a complete supplied integer tuple. Public builders return defensive copies of private caches.

Author writer and fresh receipt replay cover15 source forms from three relator lists and m=0,...,4. They include repeated and trivial relators,180 signed arbitrary-assignment corrections,90 full parent-zero round trips,90 corrupted boundary rejections,19,530 exhaustive integer selector tuples in dimensions1–6, and150 malformed caller/packet rejections. The receipt includes an exact one-cell parent/new witness pair. No numerical universal group presentation or unbounded proof compression is supplied.

Independent cross-review checked 16 ledgers, 208 retained row identities,
72 removed zero rows, 24 selector identities, 128 signed corrections,
64 zero bijections, 256 corrupted boundaries, 544 malformed transfer calls
and 32 cache-isolation cases. It also independently applied the guard patch,
checked 62 rejected malformed inputs and two unchanged sparse exports, and
replayed the entire original suite on that patched copy. Root integration
review separately checked 12 forms, 96 corrections and 48 malformed packets.
No unresolved finding remained in these reviews.

From the repository root:

```sh
/tmp/diophantine-research-venv/bin/python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/van_kampen_selector_sphere_projection.py
```

Normal execution recomputes and compares the receipt; `--write` regenerates it. The successful status is `PASS_VAN_KAMPEN_SELECTOR_SPHERE_PROJECTION`.

## 7. A separate reviewable upstream guard patch

The delivered archive is unchanged. Independent review found two public-API defects outside the parent theorem's valid integer domain:

* A floating identity matrix passed `unchart`. With relator `'ab'*30`, the DAG compiler introduced rounded coefficients; `export` then converted them to integers. The exported polynomial accepted a boundary matrix with determinant `−69402857361589764505112412160`, contradicting the intended subgroup typing.
* The numeric zero-budget checker returned an empty residual list for a malformed empty boundary because `zip` silently truncated before dimension validation.

The [upstream patch](van_kampen_exact_input_guards.patch) adds exact integer matrix/chart checks, exact budget/label/child-index checks, complete numeric witness dimensions including the zero-budget arrays, and exact polynomial-symbol/coefficient checks before export. It targets `code/van_kampen.py` relative to an extracted copy, rather than replacing the delivered ZIP or changing this transfer's pinned parent.

For a review copy extracted under `/tmp/van_kampen_review/arithmetic_van_kampen`, run from the repository root:

```sh
patch -p1 -d /tmp/van_kampen_review/arithmetic_van_kampen \
  < Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/van_kampen_exact_input_guards.patch
/tmp/diophantine-research-venv/bin/python \
  /tmp/van_kampen_review/arithmetic_van_kampen/code/verify.py \
  --receipt /tmp/van_kampen_patched_receipt.json
```

The patch was applied successfully to a private copy and the entire delivered author suite passed with every mathematical count unchanged. A separate focused replay rejected68 malformed inputs, confirmed both canonical sparse example exports are unchanged, checked the exact zero-budget identity and retained signed-integer selector behavior. Session records are `/tmp/review_van_kampen_guard_patch.{py,json}` and `/tmp/van_kampen_patched_author_receipt.json`; the original review is `/tmp/review_arithmetic_van_kampen.md`. These temporary records are provenance, not dependencies of the new replay.
