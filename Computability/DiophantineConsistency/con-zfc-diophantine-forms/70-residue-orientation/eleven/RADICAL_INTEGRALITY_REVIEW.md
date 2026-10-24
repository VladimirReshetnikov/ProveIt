# Independent review of the three-root and denominator lemmas

**Packaging scope note, added by the construction author.** The abstract
radical and denominator arguments in this note apply to the final circuit.
The later concrete-majorant discussion records an earlier, larger choice
of Rhat and Vbar. The final component uses Rhat=q^3(q+F+alpha) and
Vbar=Df(cT+Rhat); its complete proof and the separate final
`INDEPENDENT_REVIEW.md` supersede that earlier majorant specialization.
Both simplified formulas are validated there using the authentic mask
bounds and the positive integer gap Rhat-|R|. No other radical or
denominator definition changes.

Scope: the proposed eleven-positive-variable extension, reviewed independently
of its polynomial builder. This note does not certify the entire proposed
equation. It certifies the two logical implications below, with their stated
hypotheses. No frozen component has been edited.

## 1. Three-root rationality

**Lemma.** Let `a,b,c` be pairwise distinct nonnegative rational numbers.
Choose signs `epsilon_1,epsilon_2,epsilon_3` in `{−1,1}`. If

\[
t=\epsilon_1\sqrt a+\epsilon_2\sqrt b+\epsilon_3\sqrt c
\]

is a nonzero rational number, then all three square roots are rational.
Consequently it suffices to assume that `t` is rational and that one root
magnitude is strictly larger than the sum of the other two.

**Proof.** Discard zero roots temporarily; they are rational. Put all the
remaining roots in the multiquadratic splitting field

\[
K=\mathbb Q(\sqrt a,\sqrt b,\sqrt c),\qquad
G=\operatorname{Gal}(K/\mathbb Q).
\]

For each nonzero root `r`, the rule
`sigma(r)=chi_r(sigma) r` defines a character `chi_r:G->{−1,1}`.
This character is trivial exactly when `r` is rational. Two nonzero roots
have the same character exactly when their ratio is rational, equivalently
when their nonzero radicands have the same class in
`Q^*/(Q^*)^2`. No assumption that the three square classes are independent
is made.

For every character `chi`, character orthogonality gives a projection

\[
\Pi_\chi(z)=\frac1{|G|}\sum_{\sigma\in G}
                  \chi(\sigma)\sigma(z).
\]

If `chi` is nontrivial, `Pi_chi(t)=0`, whereas the projection of the signed
root sum is the sum of precisely those signed roots carrying `chi`.
Thus the signed roots in each nontrivial character class must cancel.

A class containing one term cannot cancel. A class containing two terms
can cancel only when their magnitudes are equal, which makes their
radicands equal and contradicts pairwise distinctness. A class containing
three terms contains every nonzero root; its cancellation makes the
whole sum zero, contrary to `t != 0`. Therefore no nontrivial character
occurs, and every root is rational. This also covers zero radicands.

For the consequence, strict dominance implies

\[
|t|\ge r_{\max}-\sum_{r\ne r_{\max}}r>0
\]

for every sign choice. Apply the first statement. QED.

### Exhaustive coincidence cases

* All roots have trivial square class: they are already rational.
* A nontrivial class occurs once: its character projection is nonzero.
* A nontrivial class occurs twice: cancellation forces equal radicands;
  a third irrational root in a different class would additionally be a
  forbidden singleton.
* All three roots have the same nontrivial class: rationality of their
  signed sum forces that sum to be zero. With three positive magnitudes,
  cancellation forces the largest magnitude to equal the sum of the
  other two. Strict dominance excludes this case.

The field proof remains valid when one square class is the product of
the other two. Such classes give distinct characters, so the relation
between classes does not permit additive cancellation.

### Necessary-hypothesis checks

Dominance without distinctness fails: `3 + sqrt(2) - sqrt(2) = 3`, while
`3 > 2 sqrt(2)`. Distinctness without exclusion of zero also fails:
`sqrt(2) + sqrt(8) - sqrt(18) = 0`. These are precisely the two obstructions
that the proposed hypotheses exclude.

## 2. Recovery of integral roots

**Lemma.** Suppose `D_tau,D_f,Q,V,M,S` are integers, `M != 0`, `Q != 1`,
and `gcd(M,Q-1)=1`. Suppose rational numbers `tau,f,y` satisfy

\[
\tau^2=D_\tau,\qquad f^2=D_f,\qquad
(Q-1)y^2=QV^2-1,
\]

and a signed sum of the three roots is `S/M`. Then `tau,f,y` are integers.

**Proof.** A rational number with integral square is integral: if `a/b`
is reduced with `b>0` and `(a/b)^2` is integral, then `b^2` divides
`a^2`, hence `b=1`. Thus `tau,f` are integers. The signed-sum relation
implies `M y` is integral, independent of all three signs. Write `y=a/b`
in reduced form with `b>0`. Then `b` divides `|M|`. Its quadratic equation
gives

\[
(Q-1)a^2=(QV^2-1)b^2,
\]

so coprimality of `a^2,b^2` implies `b^2` divides `|Q-1|`. The assumed
coprimality forces `b=1`. QED.

### Proposed arithmetic specialization

For integer parameters with

\[
I=i q(q-1)c^2,\qquad Q=\Delta^2I^2,
\qquad M=q^3(q-1),
\]

every prime divisor of `M` divides `q(q-1)`, hence divides `I` and `Q`.
It therefore does not divide `Q-1`. Thus `gcd(M,Q-1)=1` whenever
`M != 0`. This argument does not assume that `M` is squarefree or
positive. The intended positive-input bounds `q>=2` and nonzero
`Delta,i,c` also give `Q>=4`, so the denominator `Q-1` is nonzero.

## 3. Application boundary

For the three-root norm to invoke these lemmas, the main proof must
independently establish, before root recovery:

1. The three radicands are nonnegative rationals.
2. They are pairwise distinct (strict dominance already makes the
   dominant radicand distinct from each other radicand, so only the
   two smaller radicands require a separate comparison).
3. One root magnitude strictly exceeds the sum of the other two, or
   another argument excludes a zero rational transport sum.
4. The exact norm vanishes only if some signed root sum is the stated
   rational transport value. The usual product over all eight sign
   choices has this property, including repeated square classes.
5. The transport denominator divides `M` and the displayed integral
   parameters really are integers.

With these hypotheses proved, there is no radical or denominator gap.

## 4. Audit against the proposed register definitions

The draft inspected is
`root_transfer11_work/PROOF.md`, Sections 2--5, with the announced
simplification `L=3 Vbar`. All input coordinates are strictly positive.
The inequalities needed by the preceding abstract lemmas do hold
unconditionally for these definitions.

Write `t=sqrt(Dtau)`, `f=sqrt(Df)`, and `y=sqrt(Dy)`, all as positive real
roots. Positive inputs give `a>=2`, `c>=3`, `I>=c^2`, and `Delta>=15`.
Since `ell<ac` and `k<c`,

\[
1<D_\tau<D_f<Q,\qquad
t<\ell+k<(a+1)c,
\qquad f>(a+1)I\ge(a+1)c^2\ge3c^2.
\]

In particular the inequalities are strict where required; the final
`f>3c^2` is strict. Put `b=cT-R`.

* If `b=0`, then `V=-c`, and `Q>c^2` gives
  `Dy=c^2+(c^2-1)/(Q-1)<c^2+1`. Therefore `y<c+1`, whereas
  `f-t>(a+1)c(c-1)>c+1`; thus `f>t+y`.
* If `b!=0`, then `|V|>=Df-c>1`.
  The bound `f>3c^2>c+2` implies `Df-c=f^2-c>2f`.
  Since `Dy>V^2`, we have `y>|V|>=Df-c>2f>f+t`.

Thus every signed root sum is nonzero, in both cases.

The pairwise-distinction argument does not assume these roots are integral.
The already-proved `Dtau<Df` handles that pair. If the rational number `Dy`
equaled either integer `D` in `{Dtau,Df}`, then

\[
Q(D-V^2)=D-1,
\]

but `0<D-1<Q`, which is impossible. Thus all three radicands are distinct.

To make strictness in the majorant proof explicit, set

\[
A_0=(q(q-1)+\alpha)(q^2-1)+(M_C+qM_F)J>0,
\qquad B_0=F(q-1)(q^2-1)>0.
\]

Then `R=A0-B0` and `Rhat=A0+B0`, so `Rhat>|R|` strictly. Consequently

\[
\overline V=D_f(cT+\widehat R)+c>|V|,
\qquad \overline V>D_f>f.
\]

Also `Q>2` gives `Dy<2V^2`, whence `y<2|V|<2 Vbar`. Therefore the
announced simplification `L=3 Vbar` satisfies `L>f+y`. It also satisfies
`L>=k`, since `Vbar>c>k`. This validates the unconditional positivity
bound used in the signed-root transport.

Here `M=q^3(q-1)>0`, `Q>1`, and the exact `I=i q(q-1)c^2` meets the
coprimality specialization in Section 2. No exception remains in the
denominator argument.

**Result:** the concrete radical separation, radical recovery, and
integrality arguments pass this narrow independent review. Other parts of
the candidate construction are outside the scope of this note.

## 5. Optional explicit rational extraction formula

The square-class argument has a constructive counterpart. Suppose signed
real roots `alpha,beta,gamma` have distinct positive rational squares
`a,b,c` and rational nonzero sum `t`. Define the rational numbers

\[
u=\frac{t^2-a-b-c}{2},\qquad
v=\frac{u^2-ab-ac-bc}{2t}.
\]

Expansion gives `u=alpha beta+alpha gamma+beta gamma` and
`v=alpha beta gamma`. Hence

\[
\alpha=\frac{a(a+u)}{at+v},\qquad
\beta=\frac{b(b+u)}{bt+v},\qquad
\gamma=\frac{c(c+u)}{ct+v}.
\]

These denominators are nonzero: for example

\[
at+v=\alpha(\alpha+\beta)(\alpha+\gamma),
\]

and vanishing would force `a=0`, `a=b`, or `a=c`.
This gives each signed root explicitly as a rational number and supplies
an elementary alternative to multiquadratic character projections for
the strictly positive radicands of the candidate.
