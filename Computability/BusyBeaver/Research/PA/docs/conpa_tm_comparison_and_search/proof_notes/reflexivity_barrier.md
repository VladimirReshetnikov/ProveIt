# A Boolean counterinterpretation to replacing the equality witness by reflexivity

## Scope and result

Consider the numerical derivation calculus of
[`PA196/Logic/Basic.lean`](https://github.com/jamesyc/BusyBeaver/blob/407cdc356f6b586635e71ac92be394255f4bfea4/PA196/Logic/Basic.lean),
with its existing six heads, restricted propositional head, guarded gate,
modus ponens, and closed generalization. Replace only head 5

\[
  \exists x_D\,E(H,D)
\]

by the shorter reflexivity head \(E(H,H)\). Call the resulting numerical
proof calculus \(S_{\rm refl}\). **PA proves the consistency of this
modified calculus.** Consequently, assuming PA is consistent, no
PA-provable equivalence

\[
  \operatorname{Con}(S_{\rm refl})\leftrightarrow\operatorname{Con}(\mathrm{PA})
\]

is possible. This is a barrier to this particular logical simplification,
not a lower bound on the number of Turing-machine states.

The counterinterpretation is a primitive recursive Boolean valuation of
the exact numerical codes. It does not use an infinite truth predicate,
a model of PA, or a reflection principle. The accompanying bounded Python
check is a regression check; the argument below is the proof.

## Exact numerical constructors

Use the pinned source's Cantor pairing

\[
 p(a,b)=\frac{(a+b)(a+b+1)}2+b
\]

and constructors

\[
 I(a,b)=4p(a,b),\quad M(a,b)=4p(a,b)+1,\quad
 U(a,b)=4p(b,a)+2,\quad E(a,b)=4p(a,b)+3.
\]

Here the first argument of \(U\) is a label; its second argument is a
formula code. Write \(N(a)=I(a,1)\),
\(a\wedge b=N(I(a,N(b)))\), and
\(\exists_a b=N(U(a,N(b)))\).
The pairing convention is also specified in
[`M6/Source/Cantor.lean`](https://github.com/jamesyc/BusyBeaver/blob/407cdc356f6b586635e71ac92be394255f4bfea4/M6/Source/Cantor.lean).

Every nonzero code has a unique residue and a unique decoded pair. Both
components are smaller than the nonzero compound code. Code zero is the
single special case: \(I(0,0)=0\).

## The valuation

Define \(J:\mathbb N\to\{\bot,\top\}\) by

\[
\begin{aligned}
 J(0)&=\top,\\
 J(I(a,b))&=J(a)\Rightarrow J(b),\\
 J(M(a,b))&=
   \begin{cases}\bot,&a=b,\\J(a),&a\ne b,\end{cases}\\
 J(U(a,b))&=J(b),\\
 J(E(a,b))&=(a=b).
\end{aligned}
\]

The implication clause is used as a recursive clause only for nonzero
codes. Its zero instance is nevertheless satisfied: when
\(I(a,b)=0\), injectivity of pairing gives \(a=b=0\), and
\(J(0)\Rightarrow J(0)=\top=J(0)\). Thus the displayed constructor
identities hold for **all** natural arguments.

The other small aliases cause no problem:

\[
 J(1)=J(M(0,0))=\bot,\qquad
 J(2)=J(U(0,0))=J(0)=\top,\qquad
 J(3)=J(E(0,0))=\top.
\]

In particular, the machine's contradiction code 1 remains false. Negation,
conjunction, and existential quantification have valuations

\[
 J(N(a))=\neg J(a),\quad J(a\wedge b)=J(a)\land J(b),\quad
 J(\exists_a b)=J(b).
\]

Quantifiers therefore act as the identity on Boolean values. This is a
valuation of the numerical proof calculus, not a claim that it is an
ordinary one-sorted first-order interpretation of equality.

The definition is primitive recursive. Decode the residue and Cantor pair
by bounded search and compute the list \(J(0),\ldots,J(n)\) by course-of-values
recursion. Each lookup is into an earlier entry. A primitive recursive
coding of finite Boolean lists makes this ordinary primitive recursion.
PA proves the defining equations and totality by induction. The possibly
large numerical size of a formula code is irrelevant to this finitary
argument.

## Validity of the modified axioms and rules

For a code \(A\), write \(j_A=J(A)\).

1. **Head 1.** The value of
   \((\exists x_D\,U(D,H))\to H\) is \(j_H\Rightarrow j_H\).

2. **Head 2.** Both \(U(D,U(A,H))\) and \(U(A,U(D,H))\) have value
   \(j_H\), so the implication between them is true.

3. **Head 3.** For
   \(M(H,D)\to(E(H,A)\to M(A,D))\), if \(H\ne A\), the inner
   antecedent has value false. If \(H=A\), the two membership codes
   are identical. The head is true in either case.

4. **Head 4.** For
   \(E(H,D)\to(M(A,H)\to M(A,D))\), if \(H\ne D\), the outer
   antecedent is false. If \(H=D\), the two membership codes are
   identical. The head is true in either case.

5. **Replacement head 5.** \(J(E(H,H))=\top\).

6. **Head 6.** The value of
   \(U(D,A)\to(U(D,I(A,H))\to U(D,H))\) is
   \(j_A\Rightarrow((j_A\Rightarrow j_H)\Rightarrow j_H)\), a Boolean
   tautology.

7. **The restricted propositional head.** Its value is the classical
   tautology
   \[
   ((j_C\Rightarrow j_U)\Rightarrow j_A)\Rightarrow
   ((j_A\Rightarrow j_C)\Rightarrow(j_B\Rightarrow j_C)).
   \]
   Thus it is valid for every choice of values; the numerical restriction
   \(u\le a\) is not needed for this validity check.

8. **Modus ponens and generalization.** If \(J(a)=\top\) and
   \(J(I(a,b))=\top\), then \(J(b)=\top\). If \(J(b)=\top\), then
   \(J(U(a,b))=J(b)=\top\), for every label \(a\).

The original head 5 fails this valuation when \(H\ne D\):

\[
 J(\exists x_D\,E(H,D))=J(E(H,D))=\bot.
\]

Hence the argument does not accidentally prove consistency of the original
PA196 calculus inside PA.

## Validity of every guarded gate

For the exact gate in the pinned source, set

\[
\begin{aligned}
 \Delta&=E(a,b)\to U(c,E(a,b)),\\
 V&=M(a,b)\to U(c,M(a,b)),\\
 P&=c\to M(c,b),\\
 S&=U\bigl(b,(M(a,b)\to P)\wedge(M(c,b)\to c)\bigr),\\
 Q&=U(c,S\to N(P)),\\
 F&=N\bigl(\Delta\to(V\to Q)\bigr).
\end{aligned}
\]

Suppose the gate guard \(c\ne a\) and \(c\ne b\) holds. Because
\(c\ne b\), the valuation of \(M(c,b)\) is exactly \(J(c)\). Thus

\[
 J(P)=\top,\qquad J(M(c,b)\to c)=\top,\qquad J(S)=\top.
\]

It follows that \(J(Q)=\bot\). The values of \(\Delta\) and \(V\)
are both true, since quantification leaves values unchanged. Therefore
\(J(F)=\top\). This argument actually uses only \(c\ne b\), and
therefore proves validity under the source's stronger two-part guard.

If the source command's guard fails, it returns code zero, which is also
true under \(J\).

## Internal consistency and the obstruction

Choose any usual primitive recursive coding of finite derivation trees of
\(S_{\rm refl}\). All axiom tests, side conditions, and inference checks
are primitive recursive. PA proves, by induction on a coded derivation,

\[
 \forall p\,\forall a\,
 \bigl(\operatorname{Proof}_{S_{\rm refl}}(p,a)\to J(a)=\top\bigr).
\]

Every step is one of the explicit Boolean identities above. Since PA also
proves \(J(1)=\bot\), it proves

\[
 \neg\exists p\,\operatorname{Proof}_{S_{\rm refl}}(p,1),
\]

which is \(\operatorname{Con}(S_{\rm refl})\).
If PA also proved equivalence of this sentence with its usual consistency
sentence, PA would prove its own consistency. Gödel's second
incompleteness theorem excludes that when PA is consistent.

For a correctly implemented enumeration machine whose halting is
PA-provably equivalent to an \(S_{\rm refl}\) derivation of code 1, the
same argument gives a PA proof of nonhalting. Such a machine therefore
cannot have the requested PA-provable equivalence with
\(\operatorname{Con}(\mathrm{PA})\), under the same assumption.

## Verification artifact

`check_reflexivity_barrier.py` independently implements the exact Cantor
coding and this numerical valuation, checks all modified heads and all
guarded gates on a small exhaustive parameter box, and checks that the
original witness head fails for distinct labels. It also exhausts the
four Boolean parameters of the propositional head. These finite checks
guard against transcription errors; the universal proof and its PA
formalizability are supplied above. No new Lean theorem is claimed.
