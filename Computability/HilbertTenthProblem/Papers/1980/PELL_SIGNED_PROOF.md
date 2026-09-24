# A signed-congruence Pell parameter: 118 operations

Keep the packed system and replace only E17 by

\[
(of-d)^2=(G^2-1)(2r+1+jc)^2+1,
\qquad G=1+(a+1)(f^2-1).
\]

Every system unknown remains a positive integer. In particular, the
expression \(of-d\) is allowed to be signed, but \(o\) is positive.
This note establishes existential equivalence to the previous Pell block,
with \(f,i,j,o\) allowed to be re-chosen and all other values preserved.
It uses the same Pell facts as the source Lemma 2.28 and the existing
`psi_of_core` argument; it is not a claim of a newly compiled Lean theorem.

## The signed chi step-down observation

For \(a>1\), let \(\chi_a(n),\psi_a(n)\) be the positive Pell sequences.
If \(0<k\le m\) and

\[
\chi_a(n)\equiv\pm\chi_a(k)\pmod{\chi_a(m)},
\]

then

\[
n\equiv\pm k\pmod{2m}.
\]

For the plus sign this follows immediately from the ordinary chi step-down
lemma quoted after source Lemma 2.28, which gives the stronger modulus
\(4m\). For the minus sign, the Pell addition identities give

\[
\begin{aligned}
\chi_a(2m)&=2\chi_a(m)^2-1,\\
\psi_a(2m)&=2\chi_a(m)\psi_a(m),\\
\chi_a(n+2m)&=\chi_a(n)\chi_a(2m)
 +(a^2-1)\psi_a(n)\psi_a(2m)
 \equiv-\chi_a(n)\pmod{\chi_a(m)}.
\end{aligned}
\]

Thus the plus-sign lemma applies to \(n+2m\), and reducing its conclusion
modulo \(2m\) proves the assertion. No assumption on the parity of \(n\)
is needed.

## Sufficiency of the new block

Put \(B'=2r+1\), \(C=c\), \(D=d\), \(F=f\), \(E=ic^2\), and
\(H=B'+jc\). The bounds already proved for the packed system give
\(a>1\) and \(1<B'<C\), and \(B'\) is odd. E15 and E16 give positive
indices \(k,m\) such that

\[
D=\chi_a(k),\quad C=\psi_a(k),\qquad
F=\chi_a(m),\quad E=\psi_a(m).
\]

The standard divisibility fact used in source Lemma 2.28 and in
`psi_of_core` is

\[
C^2\mid\psi_a(m)\quad\Longrightarrow\quad C\mid m.
\]

Consequently \(0<k\le C\le m\). Since \(F^2-1=(a^2-1)i^2C^4\), the new
parameter satisfies

\[
G>1,\qquad G\equiv-a\pmod F,\qquad G\equiv1\pmod C.
\]

Set \(I=|of-d|\). E17 supplies a positive index \(n\) with
\(I=\chi_G(n)\), \(H=\psi_G(n)\), and \(I\equiv\pm D\pmod F\).
The integer polynomial identity \(\chi_{-a}(n)=(-1)^n\chi_a(n)\) therefore
gives \(\chi_a(n)\equiv\pm\chi_a(k)\pmod F\). The signed observation above
implies \(n\equiv\pm k\pmod{2m}\), hence \(n\equiv\pm k\pmod C\).

Also \(G\equiv1\pmod C\) gives
\(H=\psi_G(n)\equiv n\pmod C\), so \(n\equiv B'\pmod C\). Therefore
\(B'\equiv\pm k\pmod C\). Both \(B'\) and \(k\) lie strictly between
zero and \(C\): the latter follows from \(C=\psi_a(k)>k\) for \(k>1\),
and \(C>B'>1\) excludes \(k=1\).

The plus case gives \(B'=k\). The minus case gives \(B'+k=C\), which is
impossible because \(\psi_a(k)\equiv k\pmod2\) and \(B'\) is odd.
Thus \(C=\psi_a(B')\), exactly the relation required by the original Pell
block.

## Necessity and positive witnesses

Suppose \(c=\psi_a(B')\), with \(B'>1\) odd. The unique positive E15
root is \(d=\chi_a(B')\). Choose positive \(f,i\) satisfying E16 as in
the source construction. Define the new \(G\) above and set

\[
I=\chi_G(B'),\qquad H=\psi_G(B').
\]

Since \(G\equiv-a\pmod f\) and \(B'\) is odd,
\(I\equiv-d\pmod f\). Since \(G\equiv1\pmod c\),
\(H\equiv B'\pmod c\). Consequently

\[
o=(I+d)/f>0,\qquad j=(H-B')/c>0
\]

are integers; the positivity of \(j\) follows from \(G>1\), \(B'>1\), and
\(\psi_G(B')>B'\). Their definitions give \(of-d=I\) and E17. Thus
both directions preserve the required positive domains.

## The arithmetic saving

The old certificate needs three instructions jointly for \(a^2-1\) and
\(a-1\). Use those same three instructions for

\[
a_-=a-1,\quad a_+=a+1,\quad A=a_-a_+.
\]

E16 already computes \(X=A(ic^2)^2\) and checks \(f^2=X+1\). The new E17
coefficient takes only three further instructions:

\[
G_-=a_+X,\qquad G_+=G_-+2,\qquad G^2-1=G_-G_+.
\]

These replace the previous four instructions, saving one addition.
The change from \(d+of\) to \(of-d\) has no effect on certificate length.
The total is **118 operations: 68 multiplications and 50 additions**.

For exact verification, let \(F_{16}=f^2-X-1\),
\(G_s=1+(a+1)(f^2-1)\), and \(G_c=1+(a+1)X\). The program checks

\[
F_{17}^{\rm calculated}=F_{17}^{\rm source}
 +F_{16}(a+1)(G_s+G_c)(2r+1+jc)^2.
\]

It also checks every other residual, the existing E7 triangular correction,
and every serialized addition/multiplication statement exactly.
