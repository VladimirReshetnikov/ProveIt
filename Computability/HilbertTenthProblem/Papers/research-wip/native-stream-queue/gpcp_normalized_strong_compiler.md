# Normalize all three strong witnesses in the complete compiler

The complete [ordered sparse universal compiler](gpcp_ordered_sparse_tm.md)
has a successor costing **805 operations = 352 multiplications + 453
additions/subtractions**, with **125 positive existential witnesses**,
three positive program parameters, and exact degree **205092**. Its
certificate costs **734=328M+406A**, with **24 comparisons**. Supplying
the initial history value gives **808=353M+455A**, 126 witnesses, 25
comparisons, and degree **8532**.

The change normalizes the strong witness independently in the geometry,
recoder-AND, and selected-history kernels. It saves one polynomial
operation per kernel. The earlier tile order is also covered: its
[810-operation compiler](gpcp_sparse_tm_compiler.md) becomes
**807=352M+455A**, with a736-operation certificate and the same
24 comparisons,125 witnesses and degree205092. The unnormalized
808/130394 and supplied811/5204 ordered polynomials remain degree
alternatives. The separate universal87 polynomial and75-operation
certificate are unchanged.

This is a new wrapper of the frozen sources. It preserves their full
positive outer projection and therefore their ordinary-input universal
program slices. Soundness embeds a new zero into the complete parent;
completeness rebuilds fifteen native auxiliaries. It does not claim a
bijection between all positive tuples or an off-zero polynomial identity.

## 1. Eligible complete sources and the three local changes

The wrapper accepts the safely regrouped unit form of the
[complete fixed-program compiler](gpcp_complete_fixed_program_units.md),
including its sparse and ordered successors. Its actual thirteen native
norm-related registers are in the distinct namespaces

    geo__          geometry kernel;
    and__          recoder's prescribed AND kernel;
    hist__and__    common selected-history AND kernel.

Before this change, the common product contains the nine sign-safe norm
factors and the recoder checksum. The **history checksum remains a
separate comparison**, `hist__and__bs_q=1`. Raw SOS parents and the
unregrouped two-product form are explicitly rejected by this API. This
restriction is checked, not inferred from a generic packet label.

In each kernel write

\[
 A=a+2,\quad\Delta=A^2-1,\quad t=ic^2,\quad U=jc-(2r+1).
\]

Replace the old strong comparison and auxiliary coefficient by

\[
 Q=\Delta t^2,\qquad K_*=\Delta Q,\qquad
 N=f^2-Q,\qquad N_3^*=K_*(U^2-y^2)+y^2.              \tag{1}
\]

The source uses the already reviewed
[single-history rewrite](pcp_normalized_strong_history_units.md)
sequentially in the three namespaces. It appends each new `N` to the
existing whole product and deletes precisely that kernel's strong
comparison. At every stage the literal strong and auxiliary rows and
all consumers of `i,t,t^2`, the old `f^2-1`, and its coefficient are
checked before rewriting.

Let `W_*` be the resulting thirteen-factor product. All three main,
auxiliary and first-root factors remain; the three new strong factors
are added; the same single recoder checksum remains inside the product.
The new output is

\[
        W_*\left(1+\sum_j R_j^2\right)-1,              \tag{2}
\]

where the residuals are exactly the parent's residuals excluding its
three strong comparisons. In particular the sum still contains the
independent history checksum residual. Two unrestricted checksums have
not been multiplied together as a substitute for their separate signs.

## 2. Positive soundness without circular kernel typing

For every integer `a`, `Delta=(a+2)^2-1` is zero or three modulo four.
Thus each new strong factor `f^2-Delta*t^2` cannot equal `-1`, without
using any other equation or positivity classification.

At an integer zero of (2), its second factor is a positive integer, so
it and `W_*` must both equal one. Every factor of `W_*` is an integer
unit; each of the three new strong factors consequently equals one.
Restore all three old witnesses simultaneously by

\[
                 i_{{\rm old},j}=\Delta_j i_j.          \tag{3}
\]

Every other supplied coordinate is retained. This restoration is
strictly positive before any equation is used. The parents' positive
definition proofs give positive native `a` and hence `Delta` in each
kernel, even before radix, population or AND typing. Computed positive
input values and program loaders retain their old literal definitions.

For each kernel, `N=1` now gives

\[
 (i_{\rm old}c^2)^2=\Delta(f^2-1)=K_*.
\]

This restores the full old strong comparison and the exact old auxiliary
coefficient. All ten old product factors therefore recover their old
values, with product one. All other parent residuals, including both
checksums in their original places, are restored. The complete parent
theorem applies to this positive zero. No power, field, parity or index
conclusion was used in obtaining the restored parent zero.

On arbitrary signed assignments the correct audit identities are

\[
\begin{aligned}
 T_{{\rm old},j}^2-\Delta_j(f_j^2-1)&=\Delta_j(1-N_j),\\
 N_{3,j}^*-N_{3,j,\rm old}
   &=\Delta_j(1-N_j)(U_j^2-y_j^2).                    \tag{4}
\end{aligned}
\]

The checker evaluates these corrections in all three cores together,
then compares every surviving residual and the complete output with
its corrected parent formula. It never equates the two off-zero
polynomials.

## 3. A positive converse with fifteen fresh auxiliaries

At a parent positive zero, the geometry theorem and both selector
theorems independently give, in their actual native conventions,

\[
 r_j\text{ odd},\quad J_j=2r_j+1\equiv3\pmod4,
 \quad c_j=\psi_{A_j}(J_j).                           \tag{5}
\]

For geometry this is the recovered index in
[geometry47 §§2–4](group_linked_binary_geometry47.md), with the weaker
bootstrap retained by the
[complete recoder](native_binary_input_dilation129.md). The two AND
cores use [selector56 §§2–5](native_controller_binary_selector56.md).
Their heights, durations and packed indices may differ; no equality
between the three index parameters is assumed.

For each core retain all coordinates except `f,i,j,o,y`, and choose

\[
\begin{aligned}
 m&=2cJ,& f&=\chi_A(m),& i&=\psi_A(m)/c^2,\\
 T&=\Delta\psi_A(m),&y&=\psi_T(J),&U&=\chi_T(J)/T,\\
 j&=(U+J)/c,&o&=(U+c)/f.                              \tag{6}
\end{aligned}
\]

The new quotient is an integer: if `C=chi_A(J)`, the coefficient of
`sqrt(Delta)` in `(C+c sqrt(Delta))^(2c)` is `psi_A(2cJ)`. Its first
odd term is `2c^2 C^(2c-1)` and all later odd terms contain at least
`c^3`. Thus `c^2` divides the whole coefficient. All quantities are
positive by the same strict Pell growth used in the parent converse.
Odd `J` makes `U` integral, and `J=3 mod4` with `m=2cJ` gives the retained
minus congruences `U=-J mod c`, `U=-c mod f`, making `j,o` positive
integers. This is precisely the canonical construction proved for the
single-core wrapper; no new parity theorem is needed.

The source audits the dependency separation needed to perform the
three constructions simultaneously. The fifteen rebuilt coordinates
have only local native consumers. Every other product factor is
independent of them except the corresponding auxiliary norm, and every
other residual is independent except the corresponding strong and
auxiliary linear residuals. The constructions restore those local
equations explicitly. Therefore they do not change the recoder output,
program frame, terminal value, selectors, selected products, history
geometry, input padding, or either ratio slack.

Each new strong factor is one, each changed auxiliary factor is one,
and the remaining parent equations retain their values. This constructs
a new zero with the same outer coordinates and proves the converse.
It applies equally to computed or supplied initial history values, to
the generic direct/fixed/free program loaders, and to the three supplied
program parameters of the explicit universal machine. On valid universal
program slices the represented ordinary-input language is unchanged.

## 4. Exact costs and examples

Each local rewrite adds two certificate multiplications, removes one
comparison, and changes no witness count. Removing that comparison saves
one multiplication and two additions/subtractions in the finalizer.
The net polynomial change per core is therefore **+1M−2A**.
Across three cores it is **+3M−6A**, saving three
operations. No square or multiplication by a fixed numeral is free.

| Complete source | Certificate | Comparisons | Witnesses | Polynomial | Exact degree |
|---|---:|---:|---:|---:|---:|
|Sparse, computed initial value|736=328M+408A|24|125|807=352M+455A|205092|
|Sparse, supplied initial value|736=328M+408A|25|126|810=353M+457A|8532|
|Ordered sparse, computed|734=328M+406A|24|125|805=352M+453A|205092|
|Ordered sparse, supplied|734=328M+406A|25|126|808=353M+455A|8532|

The wrapper also checks both available history planners for the ordinary
odd-input machine, both initial-value interfaces, direct input, a fixed
positive program code, and a supplied positive program code. Those
tables are examples of the generic compiler, not additional explicit
universal machines. The numerical universal rows above use the complete
fixed U15 table, paid input morphism and program frame inherited from
the cited parents.

## 5. Degrees of the actual composed source

Let `e` be the loaded-input degree, `k` the bit-dilation width, `v` the
recoder AND scale degree, `nu` the history repunit-power degree, `N` its
fixed scale exponent, and `d=N*nu`. Then

\[
 v=(k+1)e+1.
\]

Here `e=1` for direct or fixed-code input and `e=2` for the supplied
multiplicative program code. For a generic computed initial value,
`nu=ke+1`; supplying it gives `nu=2`. In the explicit U15 program frame,
its extra positive prefix and suffix parameters instead give computed
`nu=k+3`, with `e=1`. The checker derives all scale degrees directly
from their actual registers before asserting these formulas.

The factor degrees are

| Kernel | Main norm | Auxiliary norm | First norm | New strong norm | Checksum inside product |
|---|---:|---:|---:|---:|---:|
|Geometry|5e+7|14e+24|3e+5|8e+14|none|
|Recoder AND|5v+7|18v+20|3v+5|8v+14|v|
|History AND|5d+7|20d−6nu+20|3d+5|8d+14|none|

The history checksum remains outside. Thus the thirteen-factor product
degree is

\[
                D_W=30e+35v+36d-6\nu+142.              \tag{7}
\]

The three main-norm cancellations are unchanged. In every core the
source identity, with `G=ga*(4a+3)`, is

\[
 (X+ac+G)^2-(a^2+4a+3)c^2
 =X^2+2Xac+2XG+2acG+G^2-(4a+3)c^2.
\]

The term `2acG` has strictly greatest degree. The checker asserts all
literal prerequisites and this strict degree inequality before using
the cancellation. For the new factors, their highest forms are

\[
 N_*=-a_*^2 i^2c_*^4,\qquad
 (N_3^*)_*=a_*^4i^2c_*^4U_*^2.                        \tag{8}
\]

In geometry `U_*=(jc)_*`; in either AND core `U_*=-2r_*`. The relevant
degrees of `U` are `e+3`, `3v+1`, and `4d-3nu+1`, respectively. These
give the auxiliary column above. All are degrees of the literal
polynomial, without imposing a zero-set equation.

After removing all three strong comparisons, the largest remaining
residual degree is

\[
                  M=\max(3v+1,\;4d-3\nu+1).           \tag{9}
\]

For each AND core attaining this maximum, its bound, native index and
auxiliary linear residuals contribute highest-square sum `6r_*^2`.
If both cores tie, both positive squares are retained. The other
residuals have strictly smaller degree. The geometry residuals are
bounded by `3e+4`, below `3v+1`. This includes the width-dominant case
where a short supplied history is smaller than the recoder scale.

Consequently the exact output degree is

\[
 \boxed{30e+35v+36d-6\nu+142
                +2\max(3v+1,4d-3\nu+1)}.             \tag{10}
\]

Its highest form is the product of the thirteen nonzero highest forms
times the described positive sum of squares. Weighted source evaluation
certifies a nonzero coefficient. The checker also evaluates actual
univariate polynomials under affine substitutions for two small composed
sources, confirming every factor and outer residual and the final
leading coefficient independently of the cancellation override.

The sparse universal source has `k=64`, `v=66`, `N=69`. Computed
`nu=67` gives `d=4623`, `D_W=168508`, `M=18292` and degree205092.
Supplied `nu=2` gives `d=138`, `D_W=7438`, `M=547` and degree8532.
The fixed rule permutation changes the gate count but not these audited
degrees. The old lower-degree alternatives are deliberately retained.

## 6. Executable checks and interface

```sh
/tmp/diophantine-research-venv/bin/python gpcp_normalized_strong_compiler.py
```

The [source](gpcp_normalized_strong_compiler.py) and
[receipt](gpcp_normalized_strong_compiler.json) expose `rewrite(old)`,
`build_for_tm`, `odd_machine`, `build_universal`, `build_ordered_universal`,
`lift`, `audit_identity`, `polynomial_source`, `ledger` and `degree_audit`.
The lift implements only the positive soundness embedding (3); it is not
called an inverse to the canonical converse.

Checks include computed/supplied inputs, direct/fixed/supplied program
codes, both history planners, a width100 short-history boundary family,
both sparse code choices and the ordered successor. Every ledger counts
the actual source gates and comparisons. Complete signed tests restore
all three old strong residuals with (4), compare every surviving
residual and product factor, and independently evaluate the resulting
whole output. The receipt includes simultaneous small canonical
three-core auxiliary fixtures, exact homogeneous audits, two full small
polynomial degree evaluations, rejection of raw/unregrouped parents,
and the complete807 schedule and805 ledger.

Finite fixtures do not materialize a complete astronomical packed-history
Pell zero. The general fifteen-coordinate extension above proves its
existence. No earlier source, table, ordinary-input contract, mask,
ratio inequality, or program-parameter convention is modified.

The author writer and fresh default replay passed, with 21 literal
ledgers/degree audits and 312 complete corrected-output identities,
including 168 signed assignments. Root independently reviewed the
positive embedding, canonical extension, dependency separation, counts
and degree proof; its only requested clarification distinguishes the
finalizer saving from the net polynomial change in Section4.
Substrates' independent full proof/source review passed with no findings.
It also derived the generic degree formula separately and ran 288
additional corrected-output identities, 144 signed, using its own literal
executor on six variants, including both ordered universal endpoints.
No review inferred positive equivalence from the finite signed fixtures.
