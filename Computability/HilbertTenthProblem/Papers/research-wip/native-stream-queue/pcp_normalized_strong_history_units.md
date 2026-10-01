# Normalize the strong witness inside a complete native history

The [complete native-unit affine history](pcp_uniform_affine_pair_units.md)
admits a further **one-operation polynomial saving**. Its certificate
gains two multiplications, its number of comparisons falls from ten to
nine, and its number of positive witnesses is unchanged. The finalizer
saves one multiplication and two additions/subtractions, giving a net
change of **+1M−2A**.

Applied to the [four-tile tag predicate](binary_tag_four_tile_history.md),
this gives **194 operations** for nonempty tile words, or
**196=93M+103A** including the initially halted singleton, with **28
positive witnesses**. The exact degrees are **1014** and **1015**,
respectively. The older 195/666 and 197/667 polynomials remain useful
degree alternatives. These tag bounds concern the complete encoded-input
predicate; no ordinary-input bridge to a fixed universal tag system is
supplied here. The separately established universal87 and certificate75
bounds are unchanged by this packet.

The wrapper also applies to the parent's generic fixed-table affine
histories. Its illustrative three-tile interleaved example changes from
193 to **192=91M+101A**, with 29 witnesses and degree1464. It represents
the same nonempty affine-word relation as its parent, for the same fixed
table and positive boundary parameters.

The new and old positive solution sets have the same projection onto
all coordinates except five native auxiliaries. Soundness is a positive
embedding. Completeness chooses fresh canonical auxiliaries. There is
no claim of a bijection between every old and new positive tuple, or of
equality between the two polynomials away from their zeros.

## 1. The literal replacement

Use the parent's native names without their `and__` prefix. In particular,

\[
 A=a+2,\quad \Delta=A^2-1,\quad c=kY+\eta,
 \quad J=2r+1,\quad U=jc-J.
\]

The supplied positive coordinate `i` changes meaning. Put

\[
 t=ic^2,\qquad Q=\Delta t^2,\qquad K_*=\Delta Q,
 \qquad N=f^2-Q.                                      \tag{1}
\]

The parent auxiliary norm unit becomes

\[
 N_3^*=K_*(U^2-y^2)+y^2.                              \tag{2}
\]

Keep its other three factors `N1,N0,Qc`, and form

\[
 W_*=N_1N_3^*N_0Q_cN.                                \tag{3}
\]

Delete the separate strong comparison and compare `W_*` with one.
Every other comparison and every positive supplied coordinate remains.
The final polynomial is

\[
 W_*\left(1+\sum_{j=1}^{8}R_j^2\right)-1,             \tag{4}
\]

where the eight residuals are exactly the parent's outer residuals
other than the full strong comparison.

The previous shared strong/auxiliary block computed
`t=i*c^2`, `t^2`, `f^2`, `f^2-1`, and `Delta*(f^2-1)` in **4M+1A**.
The new block computes `t,t^2,f^2,Q,K_*,N` in **5M+1A**. Appending `N`
to the old four-factor multiplication chain costs another multiplication.
Thus the certificate gains precisely two multiplications.

In the source the historical register `f_square_minus_one` is reused
for `N`; `R16` is reused for `K_*`. The only added registers are the
product `Q` and the extended unit product. The wrapper checks the actual
consumers of `i,t,t^2`, the old `f^2-1`, and `R16` before making this
change. The auxiliary factor retains its already paid square gap.

## 2. Positive soundness before native typing

For arbitrary integers, `Delta=(a+2)^2-1` is zero or three modulo four.
Consequently

\[
                  f^2-\Delta t^2\ne-1.                \tag{5}
\]

This assertion needs no other comparison and no power or digit typing.
At a zero of (4), its positive integer second factor must be one and
`W_*=1`. Each factor in (3) is an integer unit, so (5) gives `N=1`.

Restore the parent coordinate

\[
                       i_{\rm old}=\Delta i.            \tag{6}
\]

It is positive on every positive supplied history tuple, independently
of any equation. Indeed the parent's paid definitions give `J_rep>=0`,
`P=(B-1)J_rep+1>=1`, `q=16P^Nscale>0`, and hence `a=XY+Y>0`.
For the tag specialization, its computed terminal coordinate is also
strictly positive before any equation.

The old strong parameter is `T_old=Delta*t`. Since `N=1`,

\[
 T_{\rm old}^2=\Delta(f^2-1)=K_*.
\]

Thus the **full** old strong comparison is restored, the old auxiliary
unit equals (2), and the other three old factors are unchanged. Their
product is one. All eight remaining residuals are unchanged. This gives
a positive zero of the complete parent polynomial, which restores its
root gap, positive definitions, both strict ratio slacks and all native
typing equations by its established theorem. No conclusion from that
typing theorem was assumed while proving `N=1`.

For source audits on arbitrary signed assignments, (6) gives the exact
identities

\[
\begin{aligned}
 T_{\rm old}^2-\Delta(f^2-1)&=\Delta(1-N),\\
 N_3^*-N_{3,\rm old}
   &=\Delta(1-N)(U^2-y^2).                             \tag{7}
\end{aligned}
\]

These corrections, together with the unchanged outer residuals, are
what the checker tests. An off-zero old/new polynomial identity would
be false and is not used.

## 3. Fresh canonical completeness at the actual native index

Start with any parent positive zero. Its complete selector theorem
recovers `r` odd, `J=2r+1=3 mod4`, and `c=psi_A(J)`. These are the
native conventions of [selector56 §§2–5](native_controller_binary_selector56.md),
as imported by the positive AND wrapper and the affine history. They
are not the different direct75 half-binomial index conventions.

Retain every supplied coordinate except `f,i,j,o,y`. In particular keep
both ratio slacks, the first-root gap, all packed fields, all selected
products, and every boundary parameter. Set

\[
 m=2cJ,\quad f=\chi_A(m),\quad i=\psi_A(m)/c^2,
 \quad T=\Delta\psi_A(m).                             \tag{8}
\]

The new quotient is a positive integer. If `C=chi_A(J)`, the coefficient
of `sqrt(Delta)` in `(C+c sqrt(Delta))^(2c)` is `psi_A(2cJ)`.
Its first odd term is `2c^2 C^(2c-1)`; each later odd term contains
`c^j` with `j>=3`. Every term is divisible by `c^2`. This argument does
not assume `C=+1` or `-1` modulo a possibly composite `c`.

Use the same canonical fixed-minus auxiliary extension as the parent:

\[
 y=\psi_T(J),\quad U=\chi_T(J)/T,
 \quad j=(U+J)/c,\quad o=(U+c)/f.                     \tag{9}
\]

Odd `J` makes `U` integral. With `J=3 mod4` and `m=2cJ`, the retained
minus-branch congruences give `U=-J mod c` and `U=-c mod f`; all four
quantities in (9) are strictly positive integers. These are exactly the
canonical auxiliaries detailed in
[the binary kernel converse](native_binary_three_row_fifo58.md#3-exact-typing-and-the-fresh-positive-converse),
with the present actual `J`, and the identical divisibility extension in
[normalized87 §3](complete75_normalized_strong87.md#3-canonical-completeness-and-the-additional-divisibility).

The Pell identity gives `f^2-Delta*(ic^2)^2=1`. Also `K_*=T^2`, so
(2) is one and `U=jc-J=of-c`. All remaining parent units and residuals
retain their values. This constructs a new positive zero with precisely
the same outer coordinates, and proves the reverse projection.

## 4. Counts and exact degree

If the parent's complete raw history costs `C=M+A`, its unit successor
costs `C+3` and has a `C+32` polynomial. The present successor is

| Stage | Cost | Comparisons | Witnesses |
|---|---:|---:|---:|
|Normalized unit certificate|C+5 = (M+5)M + A A|9|unchanged|
|Integer-product polynomial|C+31 = (M+14)M + (A+17)A|one|unchanged|

The table excludes separately added boundary gates; those pass through
the wrapper unchanged. For the four-tile tag source, the raw161 history
plus its two paid endpoint gates gives a 168=83M+85A certificate with
nine comparisons and 28 witnesses. Its polynomial is 194=92M+102A.
The already proved singleton factor adds1M+1A, giving196=93M+103A.

Let `Nscale` be the paid scale exponent and `d0=2Nscale`. All supplied
coordinates have degree one. Use starred letters for the highest forms
of the actual computed native `a,c,r,q`, and set
`s_*=2*odd_half`, `k=eta+zeta`, `g=tau_gap`. The five factor degrees and
highest forms are

| Factor | Degree | Highest form |
|---|---:|---|
|N1|5d0+7|8 ga a_*^2 c_*|
|N3*|20d0+8|4 a_*^4 i^2 c_*^4 r_*^2|
|N0|3d0+5|4 w s_*^2 k (g-k) q_*^3|
|Qc|d0|q_*|
|N|8d0+14|−a_*^2 i^2 c_*^4|

The parent's cancellation in `N1` is unchanged. In the auxiliary root,
the packed index has degree `4d0-5`, exceeding `deg(jc)=d0+3` because
`d0>=14`. Thus `U_*=-2r_*`, which gives the displayed auxiliary highest
form. No zero-set comparison may be substituted when calculating this
degree.

After removing the strong residual, exactly three outer residuals have
degree `4d0-5`: the `X` bound, native index comparison, and auxiliary
linear comparison. Their highest forms are `r_*,-r_*,-2r_*` up to the
chosen comparison orientations. The sum of their squares has highest
form `6r_*^2`. All other outer residuals have smaller degree, as in the
parent's degree proof. Therefore (4) has exact degree

\[
 (37d_0+34)+2(4d_0-5)=45d_0+24=90N_{\rm scale}+24,     \tag{10}
\]

and nonzero highest form

\[
 -768\,ga\,w\,s_*^2 k(g-k)q_*^4a_*^8i^4c_*^9r_*^4.   \tag{11}
\]

The tag endpoint substitution is affine and preserves these forms.
Its `Nscale=11` yields degree1014; multiplying by the nonzero affine
singleton factor raises this to1015. Degree assertions concern the
literal source, without imposing any comparison. The source checks
every factor and outer degree and each highest coefficient under eight
positive-weight affine substitutions, rather than expanding the final
sum/product polynomial unnecessarily.

## 5. Executable scope and checks

Run

```sh
/tmp/diophantine-research-venv/bin/python pcp_normalized_strong_history_units.py
```

The [source](pcp_normalized_strong_history_units.py) and
[receipt](pcp_normalized_strong_history_units.json) preserve the frozen
parents and include eight actual ledgers, 512 complete correction/product
identities (256 signed assignments), 64 unconditional modulo-four cases,
eight full small canonical five-auxiliary extensions, and eight exact
degree/highest-form audits. The generic singleton-table and three-tile
examples use both packed layouts; the four tag examples use their actual
planner-selected sources. The receipt includes the full 196-operation
schedule. It does not materialize the enormous native witnesses of a
complete packed history. Those exist by the parametric converse above.

Only one native core is changed here. Composing several such cores and
their independent checksum constraints requires an explicitly audited
successor; no extra multi-core saving is included in these counts.

The author writer and fresh default replay passed. Root independently
reviewed the complete proof and source, reran the fresh default, and
derived all five degree formulas, the factor `6r_*^2`, and (11).
Substrates independently reviewed the proof and literal source with no
findings, including the actual native index and canonical extension.
Its separate literal executor additionally verified 384 complete
correction/product identities, 192 on signed assignments, across two new
affine tables in both layouts and two other tag programs. These reviews
confirm the stated projection and arithmetic scope; they do not claim
an all-tuples inverse or an ordinary-input universal tag bridge.
