# Terminal-row projection of the finite eager Tree certificate

The complete [pointer-product source](eager_tree_pointer_product_scout.md)
can drop its last two branch tags and last constructor field `c`, saving
**31 operations = 11 multiplications + 20 additions/subtractions** for every
saved size and cleanup mode. With cleanup enabled, external `N=8` now costs
**970 = 397M+573A**, with **99 natural witnesses, 64 residuals, and exact
degree 72**. At `N=1` the complete source costs **46 = 19M+27A**, with
**8 natural witnesses, 8 residuals, and exact degree 6**.

The [portable module](eager_tree_terminal_projection.py) and
[deterministic receipt](eager_tree_terminal_projection.json) contain all
sixteen complete sources. They authenticate the preceding Python, receipt,
and proof bytes before every public build, check, evaluation, or map, and
execute no historical compiler. The exposed range is exactly the saved
external sizes `N=1,...,8`; the formulas below describe the same uniform
external-size template. This does not remove the external size or establish
a fixed-arity universal polynomial, a new input loader, or an arithmetic
lower bound.

## Whole polynomial identities

Number rows from zero and put `l=N−1`. The parent's last three membership
residual occurrences are

\[
t_{l,3}+t_{l,4},\qquad t_{l,3}+t_{l,4},\qquad t_{l,3}.
\]

They arise from the empty products over later rows. A complete natural parent
zero is a zero of a sum of integer squares, so these residuals force
`t[l,3]=t[l,4]=0`.

The last constructor field `c_l` occurs only in the computed constructor
`k_l=F(F(a_l,b_l),c_l)`, multiplied by `t[l,4]` in that row's input equation.
The literal source confirms that it has no other surviving consumer. Once
the two terminal tags are zero, the entire parent polynomial is independent
of `c_l`. The last `u,v` coordinates were already removed by the pointer
projection; they are not reintroduced here.

Let `r` denote all retained supplied coordinates. The new source substitutes
`t[l,3]=t[l,4]=c_l=0`, folds exact constant/unit operations reached from those
changes, removes dead gates, and deletes the three zero residual occurrences.
Every remaining parent operation is retained literally after those aliases.
It performs no global CSE or additional normalization of other tags or rows.
The exact complete identities are

\[
F_{new}(r)=F_{parent}(r,0,0,0)
          =F_{parent}(r,0,0,c)
\]

for every scalar `c` and every retained scalar tuple `r`. These are polynomial
identities over the integers, rationals, or any commutative ring; they are not
identities with arbitrary values of the two deleted tags. The checker proves
both whole-source identities using exact ring-expression substitution and
zero/unit folding. It also checks every retained residual and all three
removed occurrences, preserving residual multiplicity and the complete
sum-of-squares finalizer.

## Natural zero maps and the precise fiber boundary

Restore every child tuple by adjoining `t[l,3]=t[l,4]=c_l=0`. This is an
unconditional natural map; it also has an explicitly signed integer algebra
mode. The polynomial graph identity takes each child natural zero to a parent
natural zero.

Conversely, a parent natural zero has the two tags zero, as shown above.
Deleting those tags and `c_l` gives a child natural zero because the entire
parent polynomial is independent of the old `c_l` once those tags vanish.
Thus the exact statement is the natural existential projection

\[
F_{new}(r)=0\quad\Longleftrightarrow\quad
\exists t_3,t_4,c\in\mathbb N:
F_{parent}(r,t_3,t_4,c)=0.
\]

The restoration is a section of projection on zero sets. It yields a
bijection only with the normalized parent zero slice `c_l=0`, where both
terminal tags already vanish. It is **not** a bijection with all parent zeros:
`c_l` is arbitrary there. In particular the receipt exhibits complete parent
zeros with `c_l=0` and `c_l=7` projecting to the same child zero. This distinction
is separate from the nonunique pointer lifts in the preceding projection.

The fields `a_l,b_l,t[l,0],t[l,1],t[l,2]` remain supplied. No branch type is
selected in advance. The represented natural `(program,argument,output)`
triples at each external `N` therefore remain exactly the same. The inherited
Tree semantics remain a natural-coordinate theorem; signed/rational tests
are algebraic checks rather than a broader computational interpretation.

## All costs paid

The certificate source loses exactly `8M+17A=25` operations. The removed
three residual occurrences additionally remove three squares and three
accumulator additions, for the total `11M+20A=31` saving. This includes
pruning the dead terminal constructor cones and folding the tag-zero input
terms and one-hot sums. The unchanged arithmetic, fixed numeral operations,
all remaining residuals, and full finalizer remain paid.

Let `epsilon=0` denote the parent's selective cleanup and `epsilon=1` its
existing extra constant cleanup. The complete counts are

\[
\begin{aligned}
M&=(3N^2+81N-46)/2,\\
A&=(3N^2+(131-2\epsilon)N-78)/2,\\
M+A&=3N^2+(106-\epsilon)N-62,\\
\#\text{natural witnesses}&=13N-5,\qquad
\#\text{residuals}=8N.
\end{aligned}
\]

The three ordinary input/output ports are separate from the reported
existential witness count. Every declared supplied coordinate and every
emitted arithmetic gate remains live. There is no free constructor, decoder,
unrecorded division, or multiplication folded merely because a zero equation
would make one of its arguments a unit.

With cleanup enabled:

| N | M | A | Complete operations | Witnesses | Residuals | Exact degree |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 19 | 27 | 46 | 8 | 8 | 6 |
| 2 | 64 | 96 | 160 | 21 | 16 | 12 |
| 3 | 112 | 168 | 280 | 34 | 24 | 22 |
| 4 | 163 | 243 | 406 | 47 | 32 | 32 |
| 8 | 397 | 573 | 970 | 99 | 64 | 72 |

## Exact degree, including the one-row boundary

For `N=1`, the remaining constructor-input and tag-one output residuals have
respective cubic leading forms `−t2*b²` and `−t1*(a+y)²`. Every other residual
has smaller degree. Hence the full degree-six leader is

\[
t_2^2b^4+t_1^2(a+y)^4,
\]

which is nonzero. It becomes `17*t^6` when every supplied coordinate equals the
same indeterminate `t`.

For `N≥2`, the root row is unchanged. Writing `m=N−1`, its third product
residual has the nonzero leading form

\[
(-1)^m t_{0,3}^{m+1}(u_0+v_0)^{4m},
\]

of degree `5m+1`. Every residual has degree at most that, while the changed
last-row residuals have degree at most three. Squaring gives exact complete
degree `10m+2=10N−8`; highest real homogeneous squares cannot cancel. In the
all-coordinates-equal-to-`t` specialization the complete leading coefficient
is exactly

\[
8\,2^{10m}+2^{8m}>0.
\]

The first two root product squares contribute the first term, and the third
contributes the second. The receipt propagates exact integer coefficient
arrays through every complete source, checks this coefficient and degree,
and compares them with the independent formal degree upper bound. These are
exact degrees, not degrees computed modulo tag or computation equations.

## Guarded interface and verification

Public functions are:

- `build(N, cleanup=True, root=None)` and `canonical_parent`;
- `rewrite` for the entire authenticated canonical parent packet, and
  `checked` for the entire canonical child packet;
- `polynomial_source` and `evaluate(..., signed=False)`;
- `restore_assignment(..., signed=False)`, the unconditional graph insertion;
- `project_parent_zero`, which requires an actual complete natural parent zero.

Exact Python types are enforced for sizes, modes, containers, and supplied
integer assignments; Boolean coordinates, floating values, missing/surplus
fields, and noncanonical packets are rejected. Positive-only coordinates are
not substituted for the natural domain. Every returned mutable packet,
source list, assignment, and provenance dictionary is independent of the
module's pinned constants and of later calls. No warm module or bytecode
cache is used: dependency Python is authenticated but never imported.

The writer passed sixteen complete graph identities, 576 retained-residual
identities, 48 restored-zero occurrences, sixteen separate arbitrary-`c`
identities, and sixteen exact degree certificates. It also checked 96 full
numeric graph identities, including sixteen rational assignments, and 48
unconditional natural restorations. A local exact eager evaluator supplied
66 complete natural projections and 66 normalized-slice round trips, covering
all five root rules and extra unused rows. In each of those 66 cases, changing
the parent terminal `c` to seven gives the same projected zero. These finite
fixtures supplement the quantified polynomial and natural-zero arguments.

There are seventy malformed-call rejections, fifteen defensive-copy checks,
nine warmed source/receipt/proof pin rejections across public calls, and an
optimized-Python rejection. No historical author suite is rerun, and no
universal computation witness is materialized.

Run from any working directory with the three pinned parent files under
`ROOT`:

```sh
python eager_tree_terminal_projection.py --root ROOT \
  --expect eager_tree_terminal_projection.json
```

`--root` defaults to sibling files; `--output FILE` writes a fresh deterministic
receipt. Saved comparisons are recursively type-sensitive. This is a
conventional proof with executable source checks, not a formal Lean
verification or a claim of global optimality.
