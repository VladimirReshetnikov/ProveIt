# Sharing the physical selector pack with the controller edge word

The controller and physical selection regions encode the same edge
selectors with different powers of P. Reusing the physical pack and
paying only for corrections to those exponents can remove substantial
duplicate arithmetic.

For the ten-letter example after the
[idle-free compiler](group_projective_idle_free_paths.md), the exact
rewrite saves **8 multiplications and 7 additions**. The joint result is
**229 certificate / 246 polynomial operations**, with polynomial split
**105M+141A**, six comparisons, 36 positive witnesses and exact degree
**3504**. Every retained residual and the complete polynomial are
identical on arbitrary integer supplied assignments. No witness,
comparison, ordinary input or fixed table changes.

The paid planner applies to any nonempty fixed macro table and keeps
the parent if its candidate plans are not cheaper. The displayed saving
is table-dependent; no numerical universal alphabet or smaller 75/88
universal bound is asserted.

## 1. The two linear forms already in the source

After deleting all idle selectors, write the remaining non-idle edges
as e=1,...,n. Their positive supplied hats encode `E_e=Ehat_e-1`.
Let ell_e in {0,...,7} be the physical letter label minus one. The
actual source's physical pack is

    S=selection__Sbatch=sum_e E_e P^ell_e.              (1)

The controller word is

    Hc=controller__edge_word=sum_e E_e P^p_e,           (2)

where the present parent uses p_e=e. Each E_e appears in exactly one
physical port; several edges may have the same ell_e. This is why (1)
already contains data that would otherwise be packed again in (2).

Equations (1)-(2) are polynomial identities, before any bit typing or
comparison. The source independently reconstructs each expression as a
linear polynomial in the edge hats with integer-polynomial coefficients
in a formal P. It compares every coefficient and the constant term with
the actual edge table. Treating computed P as a formal indeterminate is
legitimate: an identity proved for arbitrary P remains true after its
paid source definition is substituted.

## 2. Group by the difference in exponents

For every occurring offset d=p_e-ell_e, let

    G_d=sum_(p_e-ell_e=d) E_e P^ell_e.

The edge positions p_e are distinct, so the labels within any one group
are distinct too. Thus each group has at most eight edges, even if the
table is very large. The two forms satisfy

    S=sum_d G_d, Hc=sum_d P^d G_d,                    (3)

where (3) is only notation when d is negative. The actual source below
always uses nonnegative polynomial exponents.

Let b=min_e p_e, and choose an anchor r>=b. The planner considers b
and every occurring offset d>=b. For a group with minimum label j_d,
put

    G'_d=sum_(group d) E_e P^(ell_e-j_d).

Then the following is an ordinary polynomial identity:

    Hc=P^b * [ P^(r-b) S
         +sum_(d!=r) (P^(d+j_d-b)-P^(r+j_d-b))*G'_d ]. (4)

The first exponent in each correction is the smallest position of an
edge in that group minus b, so it is nonnegative. The second is also
nonnegative because r>=b and j_d>=0. To prove (4), expand the anchor
term across all G_d. The negative part of each correction cancels its
anchor contribution, leaving the coefficient P^p_e for every edge.
For the anchor group no correction is needed. Constant terms follow
from the same identity with E_e=Ehat_e-1.

This proof needs neither one-hot words, positivity, radix powers nor
the native Pell equations. Negative offsets are handled by the explicit
nonnegative exponents in (4), not by division by P.

## 3. Every correction is implemented by paid gates

Each G'_d is computed by a sparse Horner pack of its edge hats, followed
by subtraction of the fixed polynomial `sum P^(ell_e-j_d)`. Powers
between adjacent occupied labels are reused when already available and
otherwise constructed by charged multiplication. That mask polynomial
has degree at most seven. The varying P-powers are not fixed numerals.

The planner discovers existing P-polynomials from their actual source
instructions outside the private old edge pack. In particular the
existing dyadic powers, lane factors and repunits are reusable. A
missing coefficient polynomial is split at a power-of-two exponent,
with every multiplication and addition emitted explicitly. Literal
integer constants can be folded during compilation; multiplication by
a nontrivial fixed numeral at runtime is still paid.

Exact repeated instructions share a register, including commutative
operand order for addition and multiplication. Zero terms and products
by one are register aliases. No divisibility, bit operation, exponent
function or arbitrary polynomial evaluation is added as a primitive.
Each candidate includes the final P^b factor when needed.

The source audits that the old edge-packing registers have no consumers
outside their private fragment and Hc. It removes that fragment only
when a complete candidate is cheaper. All other source gates, positive
coordinates and comparisons are retained, and the replacement is
topologically sorted. A second exact linear-polynomial audit checks the
new Hc against (2). Therefore every downstream residual and the final
polynomial agree identically with the parent.

This planner is exhaustive only over its stated anchors and literal
coefficient/Horner plans. It is not an arithmetic-circuit lower bound.
The untouched parent remains the fallback when no saving is found.

## 4. The ten-letter reduction

The example has labels 1,2,3,4,5,6,7,8,1,2 on its ten live edges and
positions p_e=e. Eight edges have offset 1, while the last two have
offset 9. The physical pack therefore supplies the large common group.
Put

    T=Ehat_9+P*Ehat_10-(P+1).

The selected anchor is r=b=1, and (4) becomes

    Hc=P * [ S+(P^8-1)*T ].                          (5)

The existing P+1 and P^8 registers are reused. The exact new fragment is

| Computation | M | A |
|---|---:|---:|
|T: P*Ehat_10, add Ehat_9, subtract P+1|1|2|
|P^8-1|0|1|
|(P^8-1)*T, add S, multiply by P|2|1|
|Total|3|4|

The parent's separate edge pack costs 11M+11A, including its R_10
construction. Seven new gates replace 22, saving 8M+7A. Its other anchor
r=9 costs ten gates and is not chosen.

All four joint compiler switches retain their comparisons, witnesses
and exact degrees:

| Mask reuse | Computed P | Certificate / polynomial | Polynomial M / A | Comparisons / witnesses | Degree |
|---|---|---:|---:|---:|---:|
|Yes|Yes|229 / 246|105 / 141|6 / 36|3504|
|No|Yes|230 / 247|106 / 141|6 / 36|2928|
|Yes|No|229 / 249|106 / 143|7 / 37|1774|
|No|No|230 / 250|107 / 143|7 / 37|1486|

For a general table, subtract the audited saving from both parent
operation ledgers; do not assume the example's repeated-label pattern.
Because the entire polynomial is identical, its exact total degree and
highest form are unchanged without using any equation on its zero set.
The same source rewrite applies to the four-field, unshifted six-field,
shifted-X, strong-unit and joint-unit variants.

## 5. Executable evidence

The [source](group_projective_shared_selector_pack.py) and
[receipt](group_projective_shared_selector_pack.json) store 150 variant
ledgers and one full source/finalizer. Tables include empty and
single-edge cases, decreasing physical labels with negative offsets,
split macro paths, repeated physical cycles and the ten-letter example.

Across 3,600 assignments, including 1,200 signed assignments, every
retained register, every residual and the complete output agree with
the actual parent source. These checks supplement the symbolic
coefficient audit and the all-integer identity (4); they are not finite
evidence of universality for an illustrative numerical table.

Normal execution checks the saved receipt; `--write` regenerates it.
All previous sources remain unchanged and runnable. The numerical
universal alphabet and the separate 75/88 frontier retain their prior
status.

Independent review checked the proof and default receipt, then replayed
480 additional signed complete-output identities on 24 new tables across
all five compiler families. The reviewed endpoint is the unreindexed
parent above; composition with a zero-based lane geometry needs explicit
register-alias handling when the two packs coincide.
