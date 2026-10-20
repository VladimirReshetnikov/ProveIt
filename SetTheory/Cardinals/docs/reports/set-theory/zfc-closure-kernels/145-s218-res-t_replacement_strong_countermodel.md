# Replacing rho6 by T loses the required consistency strength

## Result

Let T_K be the exact native K219 calculus, except that its row

\[
\rho_6(i,A):\quad (\operatorname{Ex}_i Q_iA)\to A
\]

is replaced by

\[
\mathrm T(i,A):\quad Q_iA\to A.
\]

Here \(F=R(0,0)=1\), \(N(A)=A\to F\), and
\(\operatorname{Ex}_i A=N(Q_iN(A))\) are the **literal native
constructor definitions**, with no independent primitive negation.
Every other row and proof rule, including unrestricted rho8, the
support-bearing K bundle and its original gate, is retained.

**Theorem. ZFC proves that T_K does not derive code F.** Consequently,
assuming ZFC is consistent, this replacement cannot have the required
ZFC-provable equivalence with Con(ZFC). A correctly compiled T_K search
machine is provably non-halting in ZFC itself.

This is stronger than the preceding packet's relative temporal
countermodel, which assumed an ordinary K+IR model and separated only
theorem sets. The construction below uses only sets that ZFC itself
constructs; it does not assume Con(ZFC).

## The two-world structure

Let H be the set HC of hereditarily countable sets. Every member of H
has countably many members, H is closed under countable subsets, and
\(|H|=2^{\aleph_0}\). Within ZFC choose:

* an injection \(e:H\to 2^\omega\) with pairwise incomparable binary
  supports;
* a function \(n:H\to\omega\) all of whose fibers are uncountable.

For completeness, an injection into the reals follows by coding
countable well-founded extensional relations. An arbitrary binary
injection can be changed into an antichain injection by replacing
each bit b with the pair (b,1-b). Cardinal arithmetic then supplies a
bijection of H with \(\omega\times2^\omega\), whose first coordinate
can serve as n. These choices use only ordinary ZFC.

There are two worlds \(0\le1\), and both have domain H. Their binary
relations are

\[
R_0(x,y)\ \Longleftrightarrow\ x\in y,
\]
\[
R_1(x,y)\ \Longleftrightarrow\
x\in y\ \lor\ x=y\ \lor\ e(y)(n(x))=1.
\]

Thus \(R_0\subseteq R_1\), \(R_0\) is irreflexive, and \(R_1\) is
reflexive. Equality is genuine equality at both worlds.

For an assignment \(v:\mathbb N\to H\), interpret native implication
as ordinary Boolean implication at the current world and put

\[
Q_i A(t,v)\quad\Longleftrightarrow\quad
\text{for every }s\ge t\text{ and }x\in H,
\ A(s,v[i:=x]).
\]

Interpret native code zero as truth. This respects its exceptional
constructor identity \(I(0,0)=0\), since truth implies truth. All other
positive native codes have a strictly decreasing recursive decoding,
so the evaluation is well-defined by finite recursion. This is a
model of the numerical calculus directly; it need not agree with an
intended first-order decoder that separately names negation.

## The essential relative-falsity calculation

Native F is false at world 0 and true at world 1, independently of
every variable assignment. Therefore

\[
N(A)(0,v)=\neg A(0,v),\qquad N(A)(1,v)=\mathsf{true}.
\]

In particular, at the initial world the native existential reduces
to an ordinary existential **at that same world**:

\[
\begin{aligned}
\operatorname{Ex}_iA(0,v)
&=\neg Q_iN(A)(0,v)\\
&\Longleftrightarrow
\exists x\in H\ A(0,v[i:=x]).
\end{aligned}
\]

The final-world tests in \(Q_iN(A)\) are automatic, because every
final-world N(A) is true. At world 1 every native existential is true.

This deliberate behavior is allowed by the changed axiom list. There
is **no separately retained ex-falso row** \(F\to A\) and no explicit
irreflexivity axiom. In the original system ex falso was derived with
rho6. Adding it as an independent row would invalidate this model:
at world 1, F is true while some membership atoms are false.

## Verification of every retained logical row

The unrestricted propositional row

\[
((C\to U)\to A)\to((A\to C)\to(B\to C))
\]

is Boolean valid at either world, for arbitrary formula values.

Each \(Q_i\) is a normal reflexive operator, so distribution

\[
Q_i(A\to B)\to(Q_iA\to Q_iB)
\]

and the new T row hold. The quantifiers commute. When i and j differ,
both \(Q_iQ_j A\) and \(Q_jQ_i A\) quantify over the same later
world and the two independently varied coordinates. When i=j, each
side is identical. In fact this particular frame also makes
\(Q_iQ_i=Q_i\), although that stronger property is not needed.

The two membership substitutivity rows hold because, at each world,
membership is a uniform binary relation on object values and equality
is genuine equality.

The existence row \(\operatorname{Ex}_a E(a,b)\) holds at world 0
by choosing the value of b for a (and trivially when a=b). It holds
at world 1 because every native existential is true.

The merged equality row is

\[
E(c,a)\to(E(c,b)\to Q_{R(a,b)}E(a,b)).
\]

If both antecedents are true, the values of a and b agree. The
numerical binder \(R(a,b)=4P(a,b)+1\) is larger than a and b, so it
does not vary either endpoint. Equality is time-independent; its
quantified conclusion is therefore true. This argument allows every
coincidence among a,b,c, including equality of c with the numerical
binder.

For the enabled membership-vacuity row

\[
V(a,b,c):R(a,b)\to Q_cR(a,b),\qquad c\ne a,b,
\]

variation of c leaves the endpoints fixed and \(R_0\subseteq R_1\)
ensures persistence to the later world. Thus V holds at both worlds.

Modus ponens preserves validity at all assignments and worlds. If a
formula is valid at all assignments and worlds, then its Q_i
generalization is also valid there, so the theorem-GEN rule is sound.

## Why the native subset test becomes equality

The initial-world value of the native subset test is

\[
\operatorname{Sub}(p,u)=Q_z(R(z,p)\to R(z,u)).
\]

It is true when p=u. If p and u are distinct objects of H, antichain
coding gives a coordinate k with \(e(p)(k)=1\) and \(e(u)(k)=0\).
Choose z from the uncountable fiber \(n^{-1}(k)\), avoiding the
countable set \(p\cup u\cup\{p,u\}\). Then

\[
R_1(z,p)=\mathsf{true},\qquad
R_1(z,u)=\mathsf{false}.
\]

The final-world test therefore falsifies Sub. We have proved the exact
identity

\[
\operatorname{Sub}(p,u)(0)=\mathsf{true}
\quad\Longleftrightarrow\quad p=u.
\]

The same antichain argument also characterizes Sub at world 1, though
the K proof below only requires its initial-world value.

## Verification of the full native K bundle

Consider an enabled numerical triple \(c\ne a,b\), and let
\(\chi\) be the decoded formula with code c. Its private variable
label c is absent from \(\chi\): every label in a positive code is
strictly smaller than that code, and code zero is truth. The matrix
can be arbitrary, including modal or equality-containing formulas.

Use the exact emitted native expressions:

\[
\begin{aligned}
r&=R(b,c),&
s&=Q_c(R(c,a)\to R(c,b)),\\
w&=Q_b(\chi\to NQ_b(\chi\to Nr)),\\
u&=Q_a(s\to w),&
h&=Q_b(r\to NQ_a(\chi\to Nu)),\\
v&=R(a,b)\to Q_cR(a,b),&
j&=Q_c(h\to Nw),\\
B&=N(v\to j).
\end{aligned}
\]

At world 1, every N expression is true. Reading the definitions from
inside outward shows that w,u,h,j are true there. In particular the
whole B is true, regardless of the matrix or assignment.

At world 0, v is true by the preceding membership-vacuity argument.
The final-world body of j is automatically true. Consequently

\[
B(0,v)\quad\Longleftrightarrow\quad
\exists C\in H\ [h(0,v[c:=C])\land w(0,v[c:=C])].
\]

First suppose the public labels a and b differ. Fix all other matrix
parameters, and write \(\varphi(y,p)\) for the initial-world truth
value of \(\chi\) when output b has value y and input a has value p.
The matrix's independence from the private label c is essential here.
The relative-falsity calculation and the fact that the relevant
final-world bodies are true give

\[
W(p,C):=(\exists y\ \varphi(y,p))\to
             \exists y\ (\varphi(y,p)\land y\in C),
\]

\[
w(0)=W(p,C),\qquad
u(0)=W(y,C),
\]

\[
h(0)\quad\Longleftrightarrow\quad
\forall y\in C\ \exists p\bigl(\varphi(y,p)\land W(y,C)\bigr).
\]

The reduction of u uses Sub(p,y) iff p=y. Notice that the support
requirement \(\exists p\,\varphi(y,p)\) remains present; it has not
been deleted or silently weakened.

For a seed input p0, construct C by countable witness closure. If
the seed request has a witness, include one such witness. Whenever
an object y has been included and the request with input y has a
witness, include one selected witness of that request. Repeat for
countably many stages. If there is no seed witness, take C empty.

The resulting C is a countable subset of H, hence belongs to H.
It satisfies W(p0,C), and every y in C has an input supporting it:
either p0 at the first stage or the preceding member at a later
stage. Closure also gives W(y,C) for each y in C. Therefore h and w
are both true, proving B at the initial world.

Now suppose a=b. Bound-variable shadowing makes the active matrix
unary. The subset formula s is a quantified identity, and w has no
free occurrence of that common public label. If the unary matrix has
no witness, take C empty. Then w is vacuous and h has no members to
check. If it has a witness y, take C={y}. The witness condition w is
true, hence u is true, and the inner existential in h can use y.
This verifies the literal coincident-label case rather than assuming
distinct public variables.

The remaining low-code cases require no omission. If c=0, the matrix
is truth; if c=1, its initial-world value is false. Both have already
been covered by the closure argument. Varying label zero in a
quantifier does not change the world-dependent value of F, since
\(R_0(x,x)\) is always false and \(R_1(x,x)\) always true. Thus
private-label-zero and public-label-zero instances are safe. The
original gate prevents the private/public collisions c=a or c=b;
when disabled, the emitted axiom is truth code zero.

## Formal consequence

HC, the two relations, the two-world assignment space, and the
finite-formula satisfaction relation are all sets definable in ZFC.
The preceding verifications prove every axiom valid at both worlds
under every assignment. Induction on a finite native derivation then
proves its final formula valid there. F is false at the initial world,
so no derivation concludes F.

This proves Con(T_K) in ZFC. If a ZFC proof of
\(\operatorname{Con}(T_K)\leftrightarrow\operatorname{Con}(\mathrm{ZFC})\)
existed, ZFC would therefore prove Con(ZFC). Assuming ZFC is
consistent, the second incompleteness theorem excludes that
equivalence.

The obstruction depends on retaining only the listed numerical rows.
It does not rule out a different modal formalism with an explicit
falsity discipline or other additional axioms. It does rule out the
unmodified single-row rho6-to-T replacement as a route to the user's
calibrated machine.

## Independent finite checks

The companion `check_t_replacement_countermodel.py` uses only Python's
standard library. Its exhaustive finite algebra has two worlds, two
variable coordinates, and two values for each coordinate. It checks all
256 possible formula truth functions on that eight-point grid:

* 131,072 distribution instances;
* 512 T instances and 1,024 quantifier-commutation instances;
* 512 native-negation and 512 native-existential identities for the
  world-dependent F value (false,true);
* all 16 Boolean valuations of unrestricted rho8.

A separate three-object finite structure with a reflexive antichain
final relation checks the exact native K-template reduction in 12,264
cases, including both distinct and coincident public labels. All checks
pass; the receipt is `t_replacement_countermodel_checks.json`.

The finite structures in this checker are deliberately **not** claimed
to satisfy every K instance. They check the displayed semantic identities.
The existence of witnesses for every matrix is supplied by the
infinite HC construction and the ordinary mathematical closure proof
above, not by finite sampling.
