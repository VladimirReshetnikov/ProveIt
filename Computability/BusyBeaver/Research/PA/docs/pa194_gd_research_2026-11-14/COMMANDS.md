# Exact command semantics

The notation and numerical coding are inherited from the pinned PA corpus.
Let `p` be the corpus's Cantor pairing, with zero interpreted as the empty
numerical stack and `p(0,0)=0`. Write `[a;w]=p(a,w)` and use the corresponding
`hd` and `tl`. Iterated brackets list the next element first. Put

\[
 I(A,B)=4p(A,B),\quad M(a,b)=4p(a,b)+1,\quad
 U(a,B)=4p(B,a)+2,\quad E(a,b)=4p(a,b)+3.
\]

Write \(A\to B=I(A,B)\), \(\neg A=I(A,1)\),
\(A\wedge B=\neg(A\to\neg B)\), and
\(\exists_a A=\neg U(a,\neg A)\). Zero is the designated truth code, and one
is the contradiction code. These conventions include the numerical aliases
`[0;0]=0` and `I(0,0)=0`; neither is treated as a constructor with a distinct
nonzero tag in the executable checks.

## The AX head list

The inherited ordinary head schemes are

\[
\begin{aligned}
 h_1(D,H)&=(\exists_D U(D,H))\to H,\\
 h_2(D,c,H)&=U(D,U(c,H))\to U(c,U(D,H)),\\
 h_3(D,c,H)&=M(H,D)\to(E(H,c)\to M(c,D)),\\
 h_4(D,c,H)&=E(H,D)\to(M(c,H)\to M(c,D)),\\
 h_5(D,H)&=\exists_D E(H,D),\\
 h_6(D,c,H)&=U(D,c)\to(U(D,I(c,H))\to U(D,H)),\\
 \Gamma(B)&=B\to U(B,B),\\
 \rho(D,c,H,u)&=((H\to u)\to D)\to((D\to H)\to(c\to H)),
 \qquad u\le D.
\end{aligned}
\]

For the guarded gate, define

\[
\begin{aligned}
 V(a,b,c)&=M(a,b)\to U(c,M(a,b)), & P(a,b,c)&=c\to M(c,b),\\
 K(a,b,c)&=U\bigl(b,(M(a,b)\to P(a,b,c))\wedge(M(c,b)\to c)\bigr),\\
 Q(a,b,c)&=U(c,K(a,b,c)\to\neg P(a,b,c)),\\
 g(a,b,c)&=\begin{cases}\neg(V(a,b,c)\to Q(a,b,c)),&c\ne a\text{ and }c\ne b,\\
 0,&\text{otherwise.}\end{cases}
\end{aligned}
\]

The command store is \((t,w,d,h)\), consisting of the visible theorem,
numerical stack, offset, and cached theorem. AX has three operands \(c,x,y\).
With \(D=d+x\) and \(H=h+y\), its exact effect is

\[
 A_{c,x,y}(t,w,d,h)=
 \bigl(g(H,D,c),[\Gamma(D),h_6,h_5,h_4,h_3,h_2,h_1,
       \rho(D,c,H,d),U(c,h),t;w],0,0\bigr).
\]

The two emphasized parameter choices are the offset in \(\Gamma(D)\) and the
explicit AX parameter in \(U(c,h)\). The latter's body is the incoming cached
theorem \(h\), before the addition of \(y\). The \(\rho\) side condition holds
because \(d\le d+x\). The guarded gate is zero when either freshness test fails.
Every generated entry is congruent to zero modulo four except \(U(c,h)\),
which is congruent to two; thus no generated entry is one.

## Shift and MP

The unhalting effect of Shift is the same in all three machines:

\[
 S(t,w,d,h)=(h,\operatorname{tl}w,d,\operatorname{hd}w).
\]

PA194GD halts before that effect precisely when \(t+h=1\). PA194GDH and
PA194GDHS halt before that effect precisely when \(h=1\); they differ only in
the physical implementation. For \(b=d+x\), MP has the exact effect

\[
 M_x(t,w,d,h)=
 \begin{cases}(b,w,b,0),&h=I(t,b),\\
 (0,w,b,0),&h\ne I(t,b).
 \end{cases}
\]

Successful MP preserves the numerical stack. Both branches coincide when
\(b=0\), a fact used by the uniform discard word below.

## Derived words

Write \(A_0=A_{0,0,0}\). The following identities include the numerical
stack aliases at zero:

\[
\begin{aligned}
 \mathrm{Discard}&=M_0,\\
 \mathrm{Push}&=A_0;S^9;M_0,\\
 \mathrm{Pop}&=A_0;S^{11},\\
 \mathrm{Gen}_i&=\mathrm{Push};S;A_{i,0,0};S^{10},\\
 \mathrm{Finish}&=\mathrm{Push};S;S.
\end{aligned}
\]

For \(d=0\), Discard maps \((t,w,0,h)\) to \((0,w,0,0)\) for every cache.
Push maps \((t,w,d,h)\) to \((0,[t;w],0,0)\) for all stores.
Pop, when it returns, maps \((t,[a;w],d,h)\) to \((t,w,0,a)\).
For the sum detector it always returns. For the cached detector it halts
precisely when the old \(t=1\). Generalization maps
\((a,w,0,0)\) to \((U(i,a),w,0,0)\) for every \(a\), including \(a=1\).
Finish halts from \((1,w,0,0)\) in every variant.

In particular every diagonal instance is still available independently of
its new physical parameter:

\[
 \mathrm{Discard};A_{0,B,0};S^2;\mathrm{Pop}^8
 \quad\text{maps}\quad(t,w,0,0)\ \text{to}\ (\Gamma(B),w,0,0).
\]

For the list \((\Gamma(D),h_6,h_5,h_4,h_3,h_2,h_1)\), the one-based
\(j\)-th head selector is

\[
 \mathrm{Discard};A_{c,D,H};S^{j+1};\mathrm{Pop}^{9-j}
 \qquad(1\le j\le7).
\]

The guarded gate selector is
\(\mathrm{Discard};A_{c,D,H};\mathrm{Pop}^{10}\).
For \(u\le D\), the dominated head selector is

\[
 \mathrm{Discard};M_u;A_{c,D-u,H};S^9;\mathrm{Pop}.
\]

It returns \((\rho(D,c,H,u),w,0,0)\). These selectors use zero initial offset,
clear the cache, and preserve the original ambient numerical stack.

A proof compiler reserves a zero below the two MP premises. Once its store is
\((0,[a,I(a,b),0;w],0,0)\), the suffix

\[
 S;S;M_b;\mathrm{Pop}
\]

returns \((b,w,0,0)\), unless it has already halted on a contradiction premise
or conclusion. The sum detector can return \(b=1\); Finish detects that final
result. The cached detector detects \(b=1\) during Pop. This difference is
explicit in the executable symbolic certificates.

The all-parameter free-term identities in `check_commands.py` check these
words and the complete emitter tree; they support the full primitive-recursive
compiler and clock argument in the accompanying mathematical report.
