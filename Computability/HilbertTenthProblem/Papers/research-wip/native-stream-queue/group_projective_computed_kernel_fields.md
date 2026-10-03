# Compute positive kernel fields in the projective range compiler

Six already paid positive definitions can replace their supplied kernel
coordinates in the [complete projective range compiler](group_range_projective_compiler.md).
This removes six equations and six witnesses without adding or deleting
an arithmetic instruction from its comparison certificate. The resulting
single polynomial saves **18 operations**. A four-definition variant saves
12 operations while retaining the parent's exact degree.

Write the parent's certificate cost as

    C = 3m+3h+p+185+f−3min(h,3),
    M = m+2h+80+f_M−d_M,
    A = 2m+h+p+105+f_A−d_A.

Here m=2^h is the padded macro-edge count, p is the paid port-sum cost,
f=f_M+f_A is the sparse flow cost, and d_M+d_A=3min(h,3) is its existing
geometric-register saving. All symbols retain their exact definitions
in the parent. The two new complete certificates have the following
ledgers; the only ordinary relation argument is still x.

| Computed kernel fields | Certificate | Equations | Positive witnesses | Single polynomial | Exact degree |
|---|---:|---:|---:|---:|---:|
|a,d,k,s|C|22|m+36|C+65 = 3m+3h+p+250+f−3min(h,3)|12m+232|
|a,c,d,k,r,s|C|20|m+34|C+59 = 3m+3h+p+244+f−3min(h,3)|24m+444|

The polynomial multiplication/addition counts respectively are

    four fields: m+2h+102+f_M−d_M,  2m+h+p+148+f_A−d_A;
    six fields:  m+2h+100+f_M−d_M,  2m+h+p+144+f_A−d_A.

For the illustrative ten-letter macro with m=16,h=4,p=4,f=19, the
certificate costs259 operations. The four-field polynomial costs324,
has52 witnesses and degree424; the six-field polynomial costs318,
has50 witnesses and degree828. That example is not a universal alphabet.
The fixed universal alphabet in the theorem remains inherited abstractly.
Neither count improves the separate complete75/88 universal bounds.

## 1. The explicit positive graph coordinates

All names in this section refer to the selection kernel. Its scale is
q=16P^(m+18), which is positive on every assignment of the remaining
positive witnesses, before imposing any comparison. Put

    X=wq, Y=sq, E=XY, H=4a+3.

The already paid definitions are

    s=2*odd_half+1,
    k=eta+zeta,
    a=Y(X+1),
    c=kY+eta,
    d=X+ac+ga*H,
    r=F0+q*F1+q²*F2+q³*F3.                     (1)

Their right sides are actual registers in the parent source, rather
than newly evaluated formulas. Its a-register uses E+Y, which is
identically Y(X+1). F0,F1,F2 and every remaining supplied coordinate
are strictly positive. F3=16*Z+8 is also positive before any equality:
Z is a sum of the nonnegative selected-output pack, the nonnegative
edge pack, and a positive shifted history pack. The hats defining the
first two packs are positive, so subtracting their respective repunits
leaves nonnegative coefficients.

Consequently every expression in (1) is strictly positive for every
positive assignment of the remaining coordinates. This claim does not
rely on Boolean selector typing, the history recurrences, Pell signs,
or the equations being removed. In the four-field variant c and r
remain supplied positive coordinates; the same positivity argument
applies to the other four expressions.

Replace each use of an erased coordinate with its existing right-side
register. Delete exactly its defining comparison and remove it from
the positive witness list. The [source](group_projective_computed_kernel_fields.py)
performs a stable topological sort of all original gates after these
substitutions. It checks that every operand is available and that the
result is acyclic. Every original arithmetic gate is retained exactly
once, with the same operation, so the certificate cost is unchanged.

## 2. A bijection on full positive solution sets

Extend any positive tuple for the new source by the expressions (1).
The extension is positive by Section1. Every remaining residual is
exactly the corresponding parent residual on this extension, and every
removed defining residual is identically zero. Thus a new solution
extends to a parent solution with the same ordinary input x.

Conversely, at a parent solution its defining comparisons give precisely
(1). Erasing those coordinates gives a new solution, and extending it
returns the same original tuple. These maps are inverse on the entire
positive solution sets, including noncanonical Pell witnesses.

In fact the residual identities hold on arbitrary integer assignments,
without positivity or equations. The complete sum-of-squares polynomial
is the parent's polynomial under the explicit graph substitution: the
erased residual squares are identically zero. The literal polynomial
schedule now has e residual subtractions, e squares, and e−1 additions,
so it costs C+3e−1 for e=22 or20. This explains the12- and18-operation
savings without treating comparisons as free in the polynomial ledger.

The parent's generic paired-action theorem therefore transfers exactly.
For the specific fixed subgroup and program constants of the
[projective endpoint theorem](group_projective_zero_mortality6.md), it
also transfers the full universal ordinary-input representation.

## 3. Exact degree, including the cost of eliminating r

Give every supplied coordinate, including x, total degree one; fixed
program numerals have degree zero. Put L=m+18 and write homogeneous
highest parts with a superscript star. In both variants

    q*=16P^L, s*=2*odd_half, k*=eta+zeta.

For the four-field variant, c and r still have degree one. The first
Pell residual has the unique greatest degree6L+8 and highest part

    w² (s*)⁴ (k*)² (q*)⁶.                         (2)

Indeed a has degree2L+2 and d has degree at most2L+3, so the main norm
and strong auxiliary norm have degrees at most4L+6. The auxiliary
normalized-index residual still has degree at most10. The outer packing
and all other residuals also have degree below6L+8. Squaring (2) gives
the exact degree12L+16=12m+232, with nonzero highest part.

In the six-field variant, c has degreeL+2 with

    c*=k* s* q*.

The newly supplied-to-computed index r has substantially larger degree.
The highest term of the eight-lane history pack is H2*P^7. The final
joined output Z includes P^(m+8) times that pack; the original selected
and controller regions have smaller degree. Hence

    F3*=16 H2 P^(L−3),
    r*=(q*)³ F3*=16⁴ H2 P^(4L−3),

of degreesL−2 and4L−2 respectively. For the normalized root
U=jc−(2r+1), its highest part is −2r*. The retained source evaluates the
auxiliary Pell residual using the actual strong-rank square
(ic²)², so its unique greatest highest part is

    i² (c*)⁴ (2r*)²,                              (3)

of degree12L+6. The y_aux terms have strictly smaller degree; all other
residuals have smaller degree as well. The square of (3) has exact
degree24L+12=24m+444. Highest squares cannot cancel in a sum of squares.
Thus erasing r is an operation/witness saving with an explicit degree
cost; no affine-substitution degree claim is made for this variant.

## 4. Executable checks

The checker tests four macro tables, including m=2,8,16, in both variants.
For each it verifies256 complete graph extensions, every computed
register, all residuals, and the full polynomial identity. In total this
is2,048 cases, with1,536 positive extensions and512 signed off-zero
identities. It verifies the exact arithmetic, comparison and witness
counts, and checks weighted univariate degree slices against the
independently derived leading forms (2) and (3).

The finite checks audit the literal source and degree calculations;
they do not prove universality by testing inputs. The parametric
positive bijection above and the two referenced parent theorems provide
that implication. Run the checker normally to compare its deterministic
[receipt](group_projective_computed_kernel_fields.json); use `--write`
only to regenerate it.
