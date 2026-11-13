# Successor rigidity with an explicit Boolean equality split

## Scope and status

This is a complete alternative axiomatization of iPRA, obtained by combining
two proved ingredients already present in the pinned ConciseIPRA article:
the projected-orbit retraction argument in `ch02_kern.tex`
(`kern:prop:rinv`, `kern:lem:rigid`, and `kern:rem:rinv-claus`) and the
explicit Boolean equality split of `ch06_disch.tex` (`disch:def:const`).
The combination below should be described as a synthesis, not an independent
breakthrough. No smaller proof-checker size is established for this theory.

## The theory

Use ordinary intuitionistic first-order logic with equality and one numerical
sort. Terms are variables, `0`, `S(t)`, `delta(s,t)`, and
`R(n,a; i,u.h)`. The recursor binds only `i,u` in `h`; all substitutions
are simultaneous and capture avoiding. Write `1 = S(0)`.

The nonlogical axioms, universally closed over their free parameters, are

\[
\begin{aligned}
 R(0,a;i,u.h)&=a,\\
 R(Sn,a;i,u.h)&=h[n/i,R(n,a;i,u.h)/u],\\
 0=1&\longrightarrow\bot,\\
 (s=t\land\delta(s,t)=0)&\lor(s\ne t\land\delta(s,t)=1).
\end{aligned}
\]

The only additional inference rule is successor rigidity:

\[
\frac{\Gamma\vdash f(0)=0\qquad
      \Gamma\vdash f(Sz)=S(f(z))}
     {\Gamma\vdash f(t)=t}\quad(\mathrm{SR}_0).
\]

Here `f(x)` is a fixed term template, with arbitrary passive numerical
parameters; `z` is fresh for `Gamma`, `t`, and those parameters. There is
no induction hypothesis in the second premise. Contexts may contain arbitrary
first-order formulas. Coverage and successor injectivity are not axioms.

## Boolean truth flags require no induction

Define the selector
\(C(v,a,b)=R(v,a;i,u.b)\), with fresh bound variables.
Its two computations are \(C(0,a,b)=a\) and \(C(Sv,a,b)=b\).
The explicit equality split and separation give

\[
\delta(s,t)=0\lor\delta(s,t)=1,
\qquad \delta(s,t)=0\longleftrightarrow s=t.
\]

For each quantifier-free formula define a term with `0` meaning true:

\[
\begin{array}{lll}
q_{s=t}=\delta(s,t),&q_\bot=1,&
q_{A\land B}=C(q_A,q_B,1),\\
q_{A\lor B}=C(q_A,0,q_B),&&
q_{A\to B}=C(q_A,q_B,0).
\end{array}
\]

Structural induction on the *finite formula in the metatheory*, using
intuitionistic disjunction elimination, proves

\[
q_A=0\lor q_A=1,\qquad q_A=0\longleftrightarrow A.
\tag{1}
\]

For implication, the already established Boolean alternative for the
antecedent decides it: in the true branch the implication is equivalent to
its consequent; in the false branch the implication holds. This uses no
arithmetical induction and no excluded-middle schema beyond the explicit
equality split and its finite quantifier-free consequences.

## Quantifier-free induction from one use of successor rigidity

Suppose
\(\Gamma\vdash A(0)\) and
\(\Gamma,A(z)\vdash A(Sz)\), where `A` is quantifier free and `z` is fresh.
Suppress its passive parameters, put \(q(n)=q_{A(n)}\), and define

\[
e(n)=C(q(n),n,0).
\]

Boolean cases from (1) give, uniformly in fresh `x`,

\[
\Gamma\vdash A(e(x)),\qquad
\Gamma,A(x)\vdash e(x)=x.
\tag{2}
\]

Indeed, if `q(x)=0`, then `A(x)` and `e(x)=x`; if `q(x)=1`, then
`e(x)=0`, so the base proves `A(e(x))`. The second implication follows
directly from (1). These give

\[
e(0)=0,\qquad e(e(x))=e(x),\qquad e(S(e(x)))=S(e(x)).
\tag{3}
\]

For the last equation, instantiate the given induction step at `e(x)`,
use the first part of (2) to obtain `A(S(e(x)))`, and then use the second
part of (2) at `S(e(x))`. Thus (3) uses the supplied step as a local
derivation; it does not invoke an induction rule.

Now set

\[
r(n)=R(n,0;i,u.S(e(u))),\qquad f(n)=e(r(n)).
\]

The recursor equations and (3) imply

\[
\begin{aligned}
 f(0)&=e(0)=0,\\
 f(Sz)&=e(S(e(r(z))))=S(e(r(z)))=S(f(z)).
\end{aligned}
\]

One application of \(\mathrm{SR}_0\) gives `f(t)=t`. Idempotence in (3)
at `r(t)` gives `e(f(t))=f(t)`; transporting along `f(t)=t` yields
`e(t)=t`. Finally, `A(e(t))` from (2) transports to `A(t)`.
This derives the full contextual quantifier-free induction rule.

All eigenvariables can be chosen outside `Gamma`, the target term, and all
passive parameters. Instantiating the step at `e(x)` leaves `Gamma`
unchanged. The template `f` contains only its distinguished variable and
the passive parameters of `A`. No eigenvariable is exported.

## Whole-domain bi-interpretation

In this theory, define \(P(n)=R(n,0;i,u.i)\). Computation gives
`P(0)=0` and `P(Sn)=n`, hence successor injectivity. The derived
quantifier-free induction applied to
\(n=0\lor n=S(P(n))\) gives numerical coverage: its zero and successor
cases follow by computation, independently of the induction hypothesis.
Every fixed primitive-recursive description compiles into `R`: the
recursion for `g,h` is
\(R(n,g(\vec p);i,u.h(i,u,\vec p))\). Its equations are the two displayed
recursor axioms. Together with derived induction this interprets iPRA on
the entire numerical domain, with actual equality.

Conversely, in iPRA each fixed `R` term is primitive recursive, and
`delta` is its usual primitive-recursive Boolean equality characteristic.
The equality split is an iPRA theorem. The rule SR0 is admissible by
equation induction on `f(n)=n`. The two interpretations therefore use the
same whole numerical domains. Equation induction gives uniqueness of
every fixed primitive recursion, so the round trip of each numerical
operation is provably equal to that operation. The split uniquely fixes
`delta` to `0` on equal arguments and to `1` on unequal arguments; hence
its round trip agrees as well. Structural induction on formulas gives
both logical round trips. The numerical isomorphisms have graph `x=y`.
In particular the theories are equiconsistent.

## Scalar-iterator variant

The entire derivation of contextual quantifier-free induction works
unchanged with scalar `I(n,a;u.h)` in place of counter-aware `R`:
both the selector and the projected orbit ignore the counter variable.
No predecessor, coverage, cycle exclusion, cancellation, or faithful
equality term derived from induction occurs in that argument. The
faithfulness of `delta` is explicitly an axiom. Counter-aware `R` is
used here for the immediate primitive-recursion compiler and the
one-line predecessor, not for the retraction argument itself.
