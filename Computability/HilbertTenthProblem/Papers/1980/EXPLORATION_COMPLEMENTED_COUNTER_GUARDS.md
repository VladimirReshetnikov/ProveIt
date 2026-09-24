# Complementing both counter guards: a 104-operation construction

Starting from the complete 106-operation system in
`EXPLORATION_FACTORED_RAW_BLOCKS.md`, complement both conceptual counter
guard masks and replace the positive top-mask parameter \(T\) by its
positive gap \(t=J-T\). This gives **104 operations: 55 multiplications
and 49 additions or subtractions**, with 34 positive unknowns and 22
equations. All twelve mask positions remain. The existing universal
frontier is still 90; this is a further reduction of the alternate
raw-counter/controller architecture.

The exact source and full schedule are in
`../verification/explore_complemented_counter_guards.py/.json`. This
successor starts from 106 with the **retained positive pair \(Z+D=H\)**.
It does not incorporate the separate elimination of \(Z\): that would
remove a premise of the preliminary bound below and requires another
proof.

The packed integer and its Pell index change. Thus this result is an
equivalence of represented input predicates, with a fresh positive Pell
construction in the converse, rather than a claim that the preceding
system's Pell coordinates remain fixed.

## 1. Source and packing

Keep the positive unknowns and sources of 106 except for renaming the
supplied \(T\) to a supplied positive \(t\), and changing the top source to

\[
 6t=(R-3)D.                                      \tag{1}
\]

For each track, the new conceptual guard field is

\[
 E_i=t-A_i\quad(i=0,1).                          \tag{2}
\]

These fields are expressions, not supplied positive unknowns. They will
be proved nonnegative after the kernel. A zero value is permitted.

Let the four program-field replacements remain

\[
\begin{aligned}
 T_C^*&=C+J-SH,&T_V^*&=V+Z_*H,\\
 B_{\rm prog}&=(1+q^2)(C+qV)+q^2[J+(qZ_*-S)H],\\
 Q&=K_-+qZ+q^2D+q^3B_{\rm prog}.
\end{aligned}
\]

The new counter block and packed integer are

\[
 G_c=(q-1)(A_0+q^2A_1)+(1+q^2)t,
 \qquad P_c=K_++q(G_c+q^4Q).                     \tag{3}
\]

Expand (3) to obtain the twelve conceptual fields, in order,

\[
 K_+,E_0,A_0,E_1,A_1,K_-,Z,D,C,V,T_C^*,T_V^*.
                                                               \tag{4}
\]

The retained packed equations are

\[
 2r+1=q^{12}+2P_c,\qquad r+\beta=q^{12}.          \tag{5}
\]

Every other source is unchanged, including \(q=2J+1\),
\(q=Wv\), \(W=R^3\), \(H(R-1)=2J\), both positive flag pairs,
the input bound, counter time equation, cyclic controller relation and
all ten fixed-sign Pell equations.

## 2. Preliminary bounds without assuming signed fields are digits

The four program-field identity and its positivity proof still apply.
The combined lower eight-field polynomial \(L_8\) is positive from the
factored expression: \(q\ge3\), \(A_i,t,K_\pm,Z,D>0\), and every
coefficient in the lower part of (3) is positive. This statement does
not require \(E_0,E_1\ge0\).

As in the 106 proof, set \(Q_*=V+(Z_*-S)H>0\). Then

\[
 P_c-Q_*q^{11}
 =L_8+Cq^8+Vq^9+(C+J)q^{10}+SH(q^{11}-q^{10})>0.
\]

The packed equations imply \(P_c\le(q^{12}-1)/2\), hence \(Q_*\le J\).
Using \(Z_*>3S\) gives \(J>SH\), so both \(T_C^*,T_V^*\) are strictly
positive before typing. Since \(L_8>0\) and the four program fields
are now positive, the top-field argument gives

\[
 T_V^*\le J,\qquad R-1>2Z_*.
\]

Thus the predecessor's intrinsic width conditions, in particular
\(R\ge9\), hold before the kernel.

The retained positive flag pairs give \(0<K_+,K_-,Z,D<H\). Equation
(1) and \(H(R-1)=2J\) sharpen the new gap bound to

\[
 0<t<\frac{(R-3)H}{6}
   =\frac{R-3}{3(R-1)}J<\frac J3.                \tag{6}
\]

Write \(A=A_0+A_1>0\), \(\delta=K_+-K_->-H\). The unchanged time
equation \(W(A+\delta)=A-2x\) implies

\[
 A<\frac{WH}{W-1}<J.
\]

In particular \(0<A_i<J\). Combining this with (6) gives the important
signed field bounds

\[
 -J<E_i<J/3.                                    \tag{7}
\]

For the program part, \(0<V<T_V^*\le J\), and the already proved fixed
ROM bounds give
\(0<V+h_sK_++h_zD<T_V^*\le J<q\). The cyclic route therefore implies
\(C<q\) exactly as in 110, before Booleanity. Finally
\(T_C^*=C+J-SH<q+J\), with its sharper bound deferred.

The positive high program fields and \(L_8>0\) also give
\(q^{11}<P_c<r<q^{12}<r^2\). Therefore all preliminary hypotheses of
the retained 43-operation kernel hold. Its proof applies to this new
index and yields that \(q\) is a power of three and
\(q^{12}\mid\binom{2r}{r}\).

## 3. The two possible borrows are excluded

Since \(r<q^{12}\), the direct native-mask theorem makes every ternary
digit of \(r\) equal to 1 or 2, with unit digit 2. The integer
\((q^{12}-1)/2\) is now the full all-one ternary word. Subtracting it
has no borrow. Equation (5) consequently says that \(P_c\) is a
Boolean ternary word with unit digit 1.

Every base-\(q\) chunk of that word is at most \(J=(q-1)/2\). Start
at its least chunk. The positive \(K_+<H<q\) is already in range,
so it has no outgoing carry. The next raw coefficient is \(E_0\).
If \(E_0<0\), (7) shows its normalized chunk is

\[
 q+E_0>q-J=J+1>J,
\]

which cannot be a Boolean chunk. Hence \(E_0\ge0\). Its upper bound
in (7) puts it below \(q\), so it is exactly its Boolean chunk and
has no carry to the next field. The following \(A_0<J\) likewise
equals its chunk. Applying the identical argument to the next field
forces \(E_1\ge0\) and identifies it with its Boolean chunk. Then
\(A_1<J\), the remaining counter/zero fields, \(C<q\), and \(V<J\)
all decode without carries.

Now \(C\) is Boolean, so \(C\le J\) and
\(0<T_C^*<2J<q\). It and \(T_V^*\le J\) decode as the last two
Boolean chunks. All twelve semantic masks have been recovered.

This argument explicitly handles the formal negative coefficients in
(4). It neither assumes that they were initially digits nor treats the
positive factored value as proving the positivity of each coefficient.

## 4. Recover the counter and controller semantics

Set \(T=J-t>0\). Define the original conceptual guards

\[
 B_i=J-E_i=A_i+T.                               \tag{8}
\]

Because each \(E_i\) is Boolean, subtracting it from the all-one word
\(J\) yields another Boolean word, without borrow. Bound (6) gives
\(E_i<J/3\), so \(B_i>0\), including when \(E_i=0\). Equation (1)
is precisely \(6(J-T)=(R-3)D\). The original top-mask and guard
relations are therefore recovered with their positive domains.

All the decoded raw outer equations now have exactly the 110/106
counter and controller meaning: head-typed signs and zero labels,
zero top digits, numerical three-counter histories from ordinary raw
input \((2x,0,0)\) to zero, full even banks, one-state ROM paths, and
the fixed cyclic-entry first-positive-return acceptance interpretation.
The unit of \(K_+\) still forces the first sign plus. These are the
decoded-history consequences of the predecessor proof; applying them
does not identify the new \(r\) with the predecessor's packed index.
Thus every positive new solution certifies acceptance of the original
input by the same fixed compiled program.

## 5. Canonical converse and the changed Pell index

Take any accepting canonical history of the 106 construction, with
the same fixed program and any sufficiently wide allowed radix. Its
complementary zero word \(D\) is positive, so \(t=J-T>0\). Replace
each old positive Boolean guard \(B_i=A_i+T\) by
\(E_i=J-B_i\). These complements are nonnegative Boolean words;
their possible zero values are allowed because they are not supplied
positive unknowns. All supplied raw tracks, flags and program
coordinates retain their strict positivity.

Construct the new packed word (4) and set
\(r=P_c+(q^{12}-1)/2\), \(\beta=q^{12}-r\). Its twelve chunks are
native, hence \(r<q^{12}\) and \(\beta>0\), and its unit digit is 2
because the first \(K_+\) digit remains 1. The last program field is
positive, yielding the same growth hypotheses as in Section 2.

If \(P_o\) denotes the old raw packing, the exact change is

\[
 P_c-P_o=J(q+q^3)-2(B_0q+B_1q^3).               \tag{9}
\]

Since \(q\) is odd, \(q+q^3\) is even. Thus (9) is even regardless
of the parity of \(J\). The predecessor's canonical index is even,
so the new index is even too. The direct native-mask theorem supplies
the required binomial divisibility, and the full even-index positive
converse of the same fixed-sign kernel constructs fresh positive Pell
auxiliaries for this \(r\). No uncharged exponentiation or reuse of
the old auxiliary tuple is asserted.

The fixed program and its prefix annotation depend only on the
represented recursively enumerable set. The input is unchanged.
Consequently the construction has the full ordinary-input universal
contract, with all new converse witnesses positive.

## 6. Two deleted additions and the necessary source correction

In the 106 low block, \((q+1)(A_0+q^2A_1)\) uses a separately
constructed \(q+1\). Formula (3) uses the existing
\(\mathtt{twice\_J}=2J=q-1\), deleting that addition. Supplying
\(t\) directly also deletes the old \(J-T\) subtraction used by the
top equation. Both multiplications remain. The resulting schedule is
\(106-2=104=55M+49A\), with the same number of unknowns and equations.

The use of \(2J\) in place of \(q-1\) must be checked modulo the
geometry, rather than as an unconditional polynomial identity. Let
\(s_0=q-2J-1\) be that retained source residual and
\(A_p=A_0+q^2A_1\). The evaluated raw register differs from the
polynomial (3) by \(-qA_p s_0\). Consequently the doubled packing
comparison has the explicit correction \(2qA_p s_0\). The complete
checker includes it, as well as the unchanged preceding-norm
correction in the auxiliary Pell comparison. Every other source
comparison is exact without additional corrections.

## 7. Evidence boundary

The full 104-operation source and all 22 comparisons are checked
symbolically. Bounded signed-window checks explicitly reject negative
guard coefficients, and exhaustive Boolean complement pairs include
zero complements and the parity identity (9).

The canonical checker constructs fresh changed-index outer tuples for
inputs 1 and 2, verifies all twelve conceptual masks, every new outer
source, positive supplied variables, unit digit, even parity, exact
central valuation and the positive-kernel growth bounds. This is not
transport of an unchanged packed integer. As elsewhere, enormous Pell
tuples themselves are provided by the general positive converse, not
numerically instantiated. Full independent proof/source reviews and
fresh complete verification pass.
