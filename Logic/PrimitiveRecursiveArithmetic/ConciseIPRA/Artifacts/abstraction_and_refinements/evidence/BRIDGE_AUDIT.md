# Independent audit of the iPRA bridge and comparison contracts

Audit snapshot: \`167c76930834c17648fcc2509ab16260da4c727d\`.
The inspected sources are the unified article and the README of
\`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA\`, plus the exact artifacts
named below. This is a written source audit, not a rebuild of the Lean library.

## 1. Main conclusion

The native scalar calculus has a substantive bi-interpretation with **full
first-order intuitionistic primitive recursive arithmetic**. Its bridge is
stronger than preservation of arithmetical consistency and stronger than a
correspondence on closed numerical equations. Both formula round trips and
both term round trips are needed and are supplied in the main article.

A checker change can inherit that bridge if its successful public proofs are
sound for the inherited calculus and every inherited public theorem still has
a certificate. Equality of all noncanonical or malformed raw acceptance
languages is unnecessary for theorem-set equivalence, but must not be claimed
without a separate operational simulation.

## 2. Exact base calculus

Terms are variables, zero, successor, and scalar iteration
\[
 I(n,a;u.h),
 \qquad I(0,a;u.h)=a,\quad
 I(Sn,a;u.h)=h[I(n,a;u.h)/u].
\]
Only \(u\) is bound, only in \(h\). In particular the body has **no automatically
available counter**. Replacing this iterator with ordinary counter-aware
primitive recursion without charging for the extra syntax or proving the
translation changes the presentation.

Native formulas are equations, \(Q_yB\), and \(D_{x,y}B\). Their ordinary readings
are
\[
 Q_yB=B(0)\to\forall yB(y),\qquad
 D_{x,y}B=\exists x(B(x,0)\to\forall yB(x,y)).
\]
The designated contradiction is \(0=S0\).

The reference kernel has Hyp, I0, IS, crossed one-template transport,
QE, DE, DI by cases, and QI by progress:
\[
 \frac{s=t\qquad h(s)=r}{r=h(t)},\quad
 \frac{Q_yB\qquad B(0)}{B(t)},\quad
 \frac{D_{x,y}B\qquad[Q_yB(b,y)]\vdots A}{A},
\]
\[
 \frac{[B(t,0)]\vdots B(t,Sz)}{D_{x,y}B},\qquad
 \frac{[E(z)]\vdots E(Sz)}{Q_yE}.
\]
Here \(E\) must be a literal equation, \(b,z\) obey the stated freshness
conditions, and the bracketed hypotheses are discharged. Contexts may contain
arbitrary formulas. There is no hidden induction rule for quantified formulas.

**Source:** \`ch01_base.tex\`, definitions labelled
\`base:def:terms\`, \`base:def:formulas\`, \`base:def:reading\`,
\`base:def:kernel\`.

## 3. Logical adequacy is explicit

Equality needs no extra primitive rule. Transporting
\(I(0,t;u.u)=t\) along itself with the identity template proves \(t=t\).
The same rule then proves symmetry, transitivity and term congruence.
Transport in a two-sided equation takes two applications. Transport in a
compound formula is established by induction on its binders.

An unused existential coordinate identifies \(D_{x,y}B(y)\) with \(Q_yB(y)\).
Consequently DI yields introduction of Q by cases for every formula, and QE
yields numerical cases. These are **case distinction**, not induction on
arbitrary formulas.

Let \(C(v,a,b)=I(v,a;u.b)\). A formula selector is obtained by recursively
pushing \(C\) through equations and padding unmatched binder prefixes by
the zero gate. The required laws are
\[
 \operatorname{Sel}(0,A,B)\dashv\vdash A,\quad
 \operatorname{Sel}(Sv,A,B)\dashv\vdash B,
\]
\[
 \vdash\operatorname{Gate}(0,A),\qquad
 \operatorname{Gate}(Sv,A)\dashv\vdash A.
\]
The padding matters: naively pushing an unused Q or D binder through an
arbitrary formula does not preserve that formula. For example, Q of a constant
body reads \(A\to A\), so it cannot serve as a vacuous universal binder.

With \(N\) the parity term, valid native logical abbreviations include
\[
 A\Rightarrow_*B=Q_y\operatorname{Sel}(y,A,B),
\]
\[
 A\wedge_*B=Q_y\operatorname{Gate}
 (y,\operatorname{Sel}(N(y),A,B)),
\quad
 \exists_*xA=D_{x,y}\operatorname{Gate}(y,A),
\]
\[
 A\vee_*B=\exists_*x\operatorname{Sel}(x,A,B),
\quad
 \forall_*xA=A(0)\wedge_*Q_xA.
\]
The article derives all intuitionistic natural-deduction rules for these
macros. The conjunction uses the selector rows at 1 and 2. The universal
quantifier uses both the zero instance and its conditional closure.

**Source:** \`ch01_base.tex\`, \`base:def:gate\`,
\`base:lem:gate\`, \`base:def:macros\`, \`base:thm:logic\`.

## 4. The ordinary intermediate theory and its indispensable assumptions

The intermediate \(T_{\mathrm{eq}}\) is intuitionistic first-order logic
with equality over scalar iterator terms. Its nonlogical principles are:

1. The two iterator equations.
2. Coverage \(x=0\vee\exists y(x=Sy)\).
3. Separation \(0=S0\to\bot\).
4. Induction for literal equations.

Equation induction is usable with arbitrary fixed side assumptions, including
quantified assumptions. Its eigenvariable is fresh in those assumptions.

Separation is not derivable from the other displayed axioms: the one-element
structure satisfies all computations, coverage and equation induction. Native
explosion from \(0=S0\) does not remove this issue, since ordinary \(\bot\) is a
distinct logical constant. The translation of ordinary \(\bot\) is the native
equation \(0=S0\); the explicit separation axiom validates the converse reading.

Coverage is likewise not a cosmetic axiom. The coordinatewise model
\(\mathbb N\times\mathbb N\) satisfies the computations, separation, and equation
induction, but \((0,1)\) is neither zero nor a successor. It even satisfies all
classical excluded-middle instances. Thus adding ordinary decidability or
claiming that equational induction supplies cases does not repair omission
of coverage.

The article's stronger symmetry obstruction deals with arbitrary
finite-dimensional changes of domain and quotient equality: an eventually
constant power retains a nonidentity involution fixing any finite tuple of
parameters, whereas an iPRA model has a definable linear order and hence no
nonidentity finite-order automorphism. A bi-interpretation with a definable
return isomorphism would inject the first automorphism group into the second.

**Sources:** \`ch01_base.tex\`, \`base:def:teq\`,
\`base:rem:sep\`, \`base:prop:split-indep\`;
\`ch10_obs.tex\`, \`obs:thm:symmetry\`.

## 5. Arithmetic adequacy does not assume a universal evaluator

The derived scalar predecessor is the technically difficult first step. The
article gives an equation-only proof of
\[
 P(0)=0,\qquad P(Sx)=x.
\]
It uses neither coverage nor separation nor a pre-existing equality test.
The shorter 57-node version has the same internal proof status but was not
the version formalized in the stated Lean development. New incoming
predecessor packages must be considered independently.

Next define truncated subtraction by iterating the predecessor and put
\[
 K(u)=C(u,1,P(u)),\qquad
 \varepsilon(a,b)=K(Sa\mathbin{\dot-}b).
\]
Coverage and separation yield the **whole-domain** equivalence
\[
 T_{\mathrm{eq}}\vdash
 \varepsilon(a,b)=0\leftrightarrow a=b.
\]
No two-valued characteristic is required: a nonzero characteristic may be
any successor. For quantifier-free formulas, the characteristic construction
\[
 \chi_{\bot}=1,\quad \chi_{s=t}=\varepsilon(s,t),
\]
\[
 \chi_{A\wedge B}=C(\chi_A,\chi_B,1),\quad
 \chi_{A\vee B}=C(\chi_A,0,\chi_B),\quad
 \chi_{A\to B}=C(\chi_A,\chi_B,0)
\]
proves \(\chi_A=0\leftrightarrow A\). The implication case uses the derived
case distinction on the numerical term \(\chi_A\), not excluded middle for
an arbitrary quantified proposition. Literal-equation induction on
\(\chi_A(n)=0\) therefore yields the exact quantifier-free induction of iPRA.

For full primitive recursion, the article builds a pairing with provable
projections:
\[
 \langle a,b\rangle=2^{a+b}+a,\qquad
 \operatorname{fst}\langle a,b\rangle=a,\qquad
 \operatorname{snd}\langle a,b\rangle=b.
\]
The projections use a saturating binary-logarithm iterator. Its proof uses
only literal-equation inductions. Pairing surjectivity is unnecessary, and
the underlying numerical domain remains the whole original domain.

For a recursion seed \(a\) and step \(g(i,v)\), take
\[
 R(n,a;i,v.g)=
 \operatorname{snd}\left(
 I(n,\langle0,a\rangle;
 w.\langle S\operatorname{fst}(w),
 g(\operatorname{fst}(w),\operatorname{snd}(w))\rangle)\right).
\]
The invariant that the first projection equals the iteration count proves
the two primitive-recursion equations. An external recursion on each finite
primitive-recursive description now gives its scalar term. There is no
single internal universal evaluator for all primitive recursive functions,
and no diagonalization problem is hidden in this compilation.

**Sources:** \`ch01_base.tex\`, \`base:thm:pred\`,
\`base:prop:pred57\`, \`base:thm:reflect\`, \`base:prop:chi\`,
\`base:thm:qfi\`, \`base:thm:pair\`, \`base:thm:primrec\`.

## 6. Why this is a bi-interpretation

Let \(\sigma\) compile each primitive-recursive symbol to its scalar term.
Let \(\tau\) compile a scalar iterator term to a primitive-recursive
description whose recursion step ignores the counter, with all free
parameters made explicit.

The term round-trip identities
\[
 T_{\mathrm{eq}}\vdash \sigma(\tau(t))=t,\qquad
 \mathrm{iPRA}\vdash\tau(\sigma(r))=r
\]
are proved by structural induction on descriptions, using iteration or
recursion uniqueness in the recursive case. In particular, numerical
agreement only on standard numerals would not suffice.

For native formulas, the ordinary reading and the logical macro translation
are likewise mutually inverse up to internal provable equivalence:
\[
 (A^\circ)^*\dashv\vdash A,\qquad
 T_{\mathrm{eq}}\vdash\varphi\leftrightarrow(\varphi^*)^\circ.
\]
Composition yields both directions of sequent preservation and both formula
round trips between the native calculus and full iPRA.

All interpretations leave variables fixed and quantifiers unrestricted.
The comparison relation for each numerical domain is \(x=y\). It is
internally total and bijective, and the term round-trip identities prove
compatibility with every operation. This is the required definable
isomorphism, not merely a metatheoretic assertion that two standard models
look alike. Equiconsistency is then immediate by transporting the designated
contradictions in both directions.

**Source:** \`ch01_base.tex\`, \`base:prop:roundtrip\`,
\`base:prop:termrt\`, \`base:thm:bridge\`.

## 7. Public guarded presentations must not be conflated with raw native ones

The very small compact programs implement a restricted public presentation.
Its root-determined introduction uses progress for every literal equation
matrix and cases for compound matrices. Some versions also restrict equality
transport to iterator-headed sources.

This does not give the same consequence relation on all raw native sequents:
the restricted transport version cannot derive \(x=z\) from \(x=y,y=z\)
for naked variables; the root-determined introduction alone cannot derive
\(D_{x,y}(y=1)\). The repository supplies counterreadings and formal
non-derivability statements.

The correct equivalence is through a guarded public translation. A typical
public atom corresponding to \(s=t\) is
\[
 D_{r,y}\bigl(C(y,0,s)=C(y,0,t)\bigr),
\]
where \(r\) is unused. It ordinarily means exactly \(s=t\). In the guarded
presentation, equality reasoning is carried out at the iterator wrappers
obtained by specializing \(y=1\). The gate can then be reintroduced by progress.
The public language can use Eq and D only, with Q kept as an internal
resource. The native-to-public theorem and its ordinary reading preserve the
bi-interpretation on this designated language.

**Sources:** README subsection “A public language for two restrictions at
once”; \`ch03_guard.tex\`; named Lean results
\`pgprf_pubD_iff_pra\`, \`tiprf_strictly_weaker\`,
\`rdprf_strictly_weaker\`.

## 8. Size records and input contracts

The root README's displayed envelope is not itself an authoritative current
census. The later \`Artifacts/479_predecessor57/README.txt\` and
\`CLAIMS.json\` report an empirical compact envelope **(248, 270, 479)**,
attained by different programs, whereas the root README still displays
(249, 271, 479). Incoming packages may further improve this. These are
attained upper bounds on an unknown optimum, never proved complexity lower
bounds.

The predecessor57 package distinguishes:

| Profile | Tokens / AST / bytes | Contract |
| --- | ---: | --- |
| Compact | 272 / 304 / 479 | Canonical closed guarded Eq/D public goal; finite exact integer/list certificate trees; no whole public grammar validation. |
| Native | 337 / 383 / 607 | Closed native Eq/D public goal validated; consumed certificate alphabet remains promised. |
| Strict | 344 / 392 / 637 | Full closed native public goal and entire JSON alphabet validated, including unused prefixes. |

A compact checker is not an arbitrary-JSON syntax validator. An end-to-end
interface must count whatever validator enforces its stated external promise.
A separate strict companion does not retroactively make its validation free
in the compact program's measurement.

Full-module metrics include input, output, scope checking and inference
machinery; normalized bytes mean CPython 3.12.14 \`ast.unparse\` output plus
one line feed. Claims must pair the exact same contract and runtime.

## 9. Scope and implementation review points

The 502_scope_audit package documents a 17-packet, 912-byte counterexample
showing that deleting the initial goal scope scan admits a false guarded
sentence ordinarily asserting \(\exists x(x=Sx)\). The scan cannot be
dropped on the ground that later substitution “will check it anyway.”

Major proofs must be checked before admitting the next eigenparameter.
Context extension and scope-floor updates must be evaluated in the stated
order. Inferred elimination majors must still have their proofs checked.
An opened D supplies the reusable conditional closure
\(B(b,0)\to\forall yB(b,y)\), not an unconditional selected instance.

Changing the full native mode test \`len(a)%2==u\` to \`3%len(a)\` loses native
atomic case introduction. The latter selector belongs to the guarded
comparison class. Thus the valid native theorem \(D_{x,y}(y=1)\) is an
essential regression case for a full native candidate.

Finite fixtures do not prove soundness, completeness, or the bi-interpretation.
They supplement a universal trace simulation or a direct checker-decoder
proof. The existing Lean derivation equivalences do not automatically verify
a new Python program.

