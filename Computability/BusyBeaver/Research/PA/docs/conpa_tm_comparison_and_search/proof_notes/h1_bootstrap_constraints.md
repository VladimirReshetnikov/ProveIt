# Why the first head needs special care

All constructors and head names below refer to
[`PA196/Logic/Basic.lean`](https://github.com/jamesyc/BusyBeaver/blob/407cdc356f6b586635e71ac92be394255f4bfea4/PA196/Logic/Basic.lean)
at commit `407cdc356f6b586635e71ac92be394255f4bfea4`.
Write \(N(B)=I(B,1)\), \(\exists_dB=N(U(d,N(B)))\), and

\[
  B(d,h)=I(\exists_d U(d,h),h).
\]

This is the existing first head. It supplies both explosion and the
negative-vacuity construction in
[`Deduction.lean`](https://github.com/jamesyc/BusyBeaver/blob/407cdc356f6b586635e71ac92be394255f4bfea4/PA196/Logic/Deduction.lean)
and
[`Vacuity.lean`](https://github.com/jamesyc/BusyBeaver/blob/407cdc356f6b586635e71ac92be394255f4bfea4/PA196/Logic/Vacuity.lean).
In particular, ordinary Boolean identities that treat code 1 as falsity
cannot automatically be used to prove equivalence after changing the
sole axiom that establishes this behavior syntactically.

## A countervaluation for several unsafe replacements

Define a second primitive recursive Boolean valuation \(K\), distinct
from the one in `reflexivity_barrier.md`, by

\[
\begin{aligned}
 K(0)&=\top,\\
 K(I(a,b))&=K(a)\Rightarrow K(b),\\
 K(U(a,b))&=K(b),\\
 K(E(a,b))&=\bot,\\
 K(M(a,b))&=(a=b=0).
\end{aligned}
\]

The zero alias is consistent, because \(I(a,b)=0\) forces
\(a=b=0\), and \(\top\Rightarrow\top=\top\).
Thus \(K(1)=\top\) and \(K(5)=\bot\), since
\(1=M(0,0)\) and \(5=M(1,0)\).
As a result, **every** formula of the form \(N(X)\) has value true.

The unchanged heads 2 and 6 become Boolean tautologies. Heads 3 and 4
have false equality antecedents. Head 5 is a negation, hence true.
The gate is a negation, hence true. The propositional head is valid;
modus ponens and generalization preserve validity.

The shorter replacement \(U(d,h)\to h\) is valid under \(K\).
So are the contraposed/dual-looking variants
\(N(h)\to U(d,N(U(d,h)))\) and
\(h\to U(d,\exists_dh)\). A replacement that moves the only copy of
the old first head inside a negative conjunction, for example a fused
negative head \(N(I(B(d,h),X))\), is also valid under \(K\).

But the original first head \(B(d,5)\) has value false: its existential
antecedent has value true and its consequent has value false.
Likewise \(I(1,5)\) has value false. Thus the modified systems described
above cannot derive the original first head or unrestricted explosion.

This is an exact nonderivability argument. It **does not** establish that
all such systems have consistency strength below PA: \(K(1)=\top\), so
this valuation alone does not prove their consistency with contradiction
code 1. A different interpretation or proof translation might conceivably
recover the desired consistency strength. The argument rules out the
proposed immediate recovery of the existing calculus and prevents a
circular use of explosion during that recovery.

Keeping the first head unchanged while fusing another positive head into
head 5 is not subject to this obstruction: the unchanged first head
already supplies explosion and double-negation elimination.

## Conservative first-head variants with an explicit recovery

The parameter \(A\) is unused in the original \(B(D,H)\), while AX
enumerates all triples \((D,H,A)\). Consequently each of the following
replacement families retains the old family by an explicit, finite
derivation:

\[
\begin{aligned}
 &A\to B(D,H),\\
 &(\exists_DU(D,H))\to(A\to H),\\
 &B(D,I(A,H)),\\
 &B(D,I(H,A)),\\
 &B(D,I(I(A,H),H)),\\
 &B(D,I(I(H,A),H)).
\end{aligned}
\]

For the first two, set \(A=0\) and use the pure implicational theorem
\(0=I(0,0)\). For the third set \(A=0\); for the fourth set \(H=0\)
and use \(A\) as the target formula. For the fifth set \(A=H\), so
the formula argument becomes \((H\to H)\to H\), which is equivalent
to \(H\) by pure implicational reasoning. In the sixth,
\((H\to A)\to H\) is equivalent to \(H\) by Peirce's law and
weakening, already available from the restricted implicational head.

For the formula-argument replacements, this pure equivalence transports
through \(U\) by generalization and head 6. It transports through
\(\exists\) by two applications of implication contraposition and one
application of universal monotonicity. Implication contraposition with
an arbitrary consequent 1 is a pure implicational theorem; this step
does not assume explosion or double-negation elimination. The transported
equivalences then turn the new first head into \(B(D,H)\).

Thus recovery of the original first head, followed by its existing
explosion proof, is noncircular. These variants add macro tokens but can
change sharing in the compiled source; they are being searched for that
reason rather than being claimed to have shorter formula syntax.

The same unused-parameter argument permits replacing head 5 by
\(A\to\exists_D E(H,D)\). If \(W=U(D,N(E(H,D)))\), the alternative
\(W\to N(A)\) is the antecedent-exchanged form. Setting \(A=0\)
recovers the old head in either case.

## A shorter fresh-label head: sound, but completeness unresolved

Another candidate is

\[
  (\exists_H H)\to H.
\]

In the PA interpretation the label \(H\) is fresh in the formula with
code \(H\): every variable label in a nonzero decoded formula is
strictly below its code, and code 0 denotes truth. The candidate is
therefore sound. It removes the inner \(U(D,H)\) from the old head and
saves four macro tokens in its direct emission.

It still supplies explosion noncircularly. Weakening gives
\(1\to(U(H,N(H))\to1)\), which is \(1\to\exists_H H\); composition
with the new head gives \(1\to H\). Classical reasoning then yields

\[
 N(H)\to U(H,N(H)).
\]

However, this is negative vacuity only at the formula's own code. It is
not a proof of vacuity at an arbitrary absent label. Even the more
generous schema \((\exists_D H)\to H\) restricted to \(D\ge H\)
does not immediately support the current completeness proof.

For example, the reverse-rewriting argument specializes
\(S=U(a,\psi(a))\) to \(\psi(b)\), where
\(\psi(b)=M(c,b)\to N(\chi(b))\), using the equality witness
\(\exists_aE(b,a)\). Its existential elimination needs negative
vacuity of \(\psi(b)\) at the label \(a\). But \(c\) is a large
separation-property code, and

\[
  \operatorname{code}(\psi(b))>c>a.
\]

The restricted schema does not provide that instance. Padding the
separation property increases \(c\) and does not resolve the inequality.
A new specialization or renaming proof is required; closure under
arbitrary renaming cannot be assumed for a numerical schema that ties a
binder label to a formula code. No PA-completeness claim is made for this
fresh-label candidate.
