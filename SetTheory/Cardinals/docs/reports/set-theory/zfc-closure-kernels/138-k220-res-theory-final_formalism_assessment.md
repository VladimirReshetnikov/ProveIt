# Formalism-side research: proved reductions and exact limitations

This note concerns the native K221 calculus at ProveIt commit `c011e44b` and
records mathematical research carried out while the original-calculus
220-state decoder candidate was being constructed. None of the unsuccessful
source experiments below is an alternative certificate for that candidate.
The winning source rotations preserve the original complete guarded control
flow, so their consistency calibration does not depend on a new logical
interpretation.

## 1. Native conventions and the scope of a countermodel

Write

\[
 P(a,b)=\frac{(a+b)(a+b+1)}2+b,\quad
 I(a,b)=4P(a,b),\quad R(a,b)=4P(a,b)+1,
\]
\[
 Q(a,b)=4P(a,b)+2,\qquad E(a,b)=4P(a,b)+3.
\]

The distinguished contradiction code is \(F=R(0,0)=1\), negation is
\(N(A)=I(A,F)\), and \(\exists_i A=N(Q_iN(A))\). Code zero is interpreted
as truth; its exceptional self-decoding as \(I(0,0)\) has the same truth
value. For every positive native formula code \(c\), every variable label
occurring anywhere in its decoded formula is strictly smaller than \(c\).
This follows by induction because all constructor fields of a positive code
are smaller than the code. The zero exception has no variable occurrences.

The following distinctions matter.

* A model of the **logical rows alone** disproves a proposed logical
  derivation. It does not settle the consistency strength after K is added.
* A model of the **full changed K calculus**, constructed assuming an
  ordinary K+IR model, can disprove exact theorem-set equivalence while leaving
  equiconsistency open.
* A model of the **full changed K calculus constructible in ZFC without
  assuming Con(ZFC)** proves its consistency in ZFC. Subject to consistency
  of ZFC, such a theory cannot have its consistency internally equivalent to
  Con(ZFC), by the second incompleteness theorem.

## 2. A rigorous full countermodel to deleting equality existence

### Statement

Delete only

\[
 \rho_1(a,b):\quad \exists_a E(a,b),
\]

or replace that enumerator row by native truth zero. Retain the classical
basis, distribution \(\rho_2\), commutation \(\rho_4\),
\(\rho_6:(\exists_aQ_a A)\to A\), membership substitutivity, merged G,
full gated membership vacuity, and the complete current K seed bundle.
ZFC proves consistency of this changed native calculus.

This result is stronger than observing that primitive equality can be empty:
it supplies an explicit model of all K instances and the retained logical
rules. Its mechanism is that different variable labels can have different
finite domains once equality existence no longer connects those domains.

### The finite domains

Define by recursion on \(n\)

\[
 U_n=\bigcup_{i<n}(\{i\}\times D_i),\qquad
 D_n=\mathcal P(U_n)\times\{0,1\}.
\]

Thus each \(D_n\) is finite, nonempty, and explicitly constructible in ZFC.
An element of \(D_n\) is a pair \((S,\epsilon)\). An assignment chooses
\(v_n\in D_n\) for every natural label \(n\). Interpret \(Q_n\) as
ordinary universal variation of coordinate \(n\) over \(D_n\).

Set every equality atom to false. For \(x\in D_i\) and
\(y=(S_y,\epsilon_y)\in D_j\), interpret the membership atom by

\[
 R_{i,j}(x,y)\quad\Longleftrightarrow\quad
 \begin{cases}
   (i,x)\in S_y,&i<j,\\
   \epsilon_y=1,&i>j,\\
   \text{false},&i=j.
 \end{cases}
\]

Implication is ordinary Boolean implication. In particular, native
\(F=R(0,0)\) is false and code zero is true.

This is an algebraic semantics for the native syntax, equivalently an
assignment model with a separate sort for each variable label. It is not
being claimed to be a one-sorted set-theoretic structure. Such a claim would
silently restore the very equality-existence principle being deleted.

### The logical rows

Distribution, commutation, and \(\rho_6\) hold because each quantifier is
ordinary universal variation of one coordinate, with a nonempty domain.
Modus ponens and theorem generalization preserve validity. Every primitive
Eq atom is false, so G and both membership-substitutivity rows are valid.
If \(c\ne a,b\), changing coordinate \(c\) does not change the value of
\(R(a,b)\); hence every required membership-vacuity row is valid. Every
same-label membership atom is false, which also supplies the required
irreflexivity interpretation. The classical basis is valid under Boolean
implication.

### Every K bundle is valid

Use the exact current source template. For matrix code \(c\), let
\(\chi\) denote its decoded formula and abbreviate

\[
 r=R(b,c),\quad s=Q_c(R(c,a)\to R(c,b)),
\]
\[
 w=Q_b\bigl(\chi\to\neg Q_b(\chi\to\neg r)\bigr),
 \qquad u=Q_a(s\to w),
\]
\[
 h=Q_b\bigl(r\to\neg Q_a(\chi\to\neg u)\bigr).
\]

The seed component of the bundle is

\[
 \neg Q_c(h\to\neg w)=\exists_c(h\wedge w),
\]

and the other component is membership vacuity. Only \(c\ne a,b\) is
assumed. The code-label bound makes \(c\) absent from \(\chi\).

First suppose \(a\ne b\). Fix the values of every other coordinate and
form the support set

\[
 S=\{y\in D_b:\text{ for some }p\in D_a,
              \chi[v_a:=p,v_b:=y]\text{ is true}\}.
\]

Choose \(C\in D_c\) such that

\[
 R_{b,c}(y,C)\quad\Longleftrightarrow\quad y\in S.
\]

Such a choice always exists. If \(b<c\), the subset component of an element
of \(D_c\) can encode any subset of the tagged copy of \(D_b\). If
\(b>c\), the code-label bound says that \(\chi\) does not mention \(b\),
so \(S\) is either all of \(D_b\) or empty, and the flag \(\epsilon_C\)
encodes the required choice. Equality \(b=c\) is excluded by the source
gate.

For this container, every witness to \(\chi(y,p)\) already belongs to
\(C\). Consequently \(w\) is true for every input value \(p\), and
\(u\) is true regardless of the subset test \(s\). Every member of
\(C\) has an input witness by the definition of \(S\), so \(h\) is true
as well. Thus \(\exists_c(h\wedge w)\) holds.

The coincidence \(a=b\) needs a separate capture check. Choose \(C\) with
full \(D_b\)-membership if \(\exists_b\chi\) is true, and with empty
\(D_b\)-membership otherwise. Both choices are available in \(D_c\),
using its subset component if \(b<c\) and its flag if \(b>c\). Then
\(w\) is true. The subset test \(s\) becomes a generalized identity
because \(a=b\), so \(u\) is true. The support clause \(h\) is then
true by the same empty/full choice. This proves the literal coincident-label
instance, without an implicit alpha-conversion or independence assumption.

The argument includes matrix code \(c=0\): its matrix is true, and all
enabled witness/input labels are positive, so the flag in \(D_0\) supplies
a full container. It also includes \(c=1\), whose matrix is the always-false
\(R(0,0)\): an empty container works. No low-label instance is omitted.

### Internal consequence

The sequence \((D_n)\), the assignment space, the truth definition for finite
native formulas, and the soundness induction on finite proofs are all
constructions available in ZFC. They give a model of every axiom code while
\(F\) is false. Hence ZFC proves that no finite native proof derives \(F\).
Removing rho1 therefore cannot be used for the requested Con(ZFC)
calibration. The native matrix/private-label coupling, which ordinarily helps
make the implementation concise, makes this countermodel possible: a matrix
with code \(c\) only inspects lower variable sorts, whose subsets can be
placed in its new private sort \(D_c\).

## 3. Replacing rho6 by T: an exact theorem obstruction, with calibration open

The tested 220-state source variant replaces

\[
 (\exists_aQ_a C)\to C
 \quad\text{by}\quad Q_a C\to C.
\]

The latter is an ordinary universal-specialization instance. The old postfix
word applies the existential constructor **before** appending the final
implication. Thus the old row is not \(\exists_a(Q_aC\to C)\); proving
existence of the new T implication does not recover the old axiom.

Raw rho6 is not derivable from the full T-modified K calculus, assuming an
ordinary K+IR model exists. To see this, let \(M\) be any such ordinary
model with nonempty membership. Add two times \(0\le1\), use the same
ordinary assignment domain at both times, interpret membership as empty at
time 0 and as membership of \(M\) at time 1, and interpret equality as
actual identity at both times. Let

\[
 Q_i A=\Box\forall_i A,
\]

where \(\Box\) ranges over current and later times. The temporal relation
is reflexive and transitive, independent of assignment variation.

These operators are normal, reflexive, and commute. Equality existence,
substitutivity, and G hold. Positive fresh membership vacuity holds because
membership only grows with time. Every K instance holds at the final time
by the model \(M\), and at the initial time because its outer existential
can choose a final-time container witnessing \(h\wedge w\). The bundled
membership vacuity also holds at both times. Native bottom is false at both
times by irreflexivity.

Choose a membership atom \(A\) true under some final-time assignment and a
binder \(i\) fresh from that atom. Initially \(A\) is false, but
\(\exists_i Q_i A\) is true by choosing the final time. Thus rho6 fails.

This is a **relative full-theory countermodel**: it uses an ordinary K+IR
model. It rules out exact recovery of rho6; it does not show that the changed
theory is weaker in consistency strength. A stable-world, saturation, or
other effective interpretation might still prove equiconsistency. No such
interpretation was established in this work. The checked finite machine
runtime for this source therefore does not by itself certify the requested
Con(ZFC) equivalence. The original-theory-preserving decoder candidate avoids
this unresolved issue.

## 4. Fusing distribution and commutation

Consider either proposed four-parameter row

\[
 Q_aQ_b(A\to B)\to(Q_aQ_bA\to Q_bQ_aB),
\]

or the variant with the premise and conclusion orders interchanged. A
four-element Boolean algebra supplies a precise logical-basis obstruction.
Identify the elements with subsets of a two-element set and let every
quantifier have table

\[
 Q(0)=1,\quad Q(\{0\})=0,\quad
 Q(\{1\})=1,\quad Q(1)=1.
\]

Here \(0\) and \(1\) denote Boolean bottom and top, not native code zero
and one. Give each membership atom value bottom and every equality atom value
\(\{1\}\). Then every \(Q^2\) is constantly top. The fused rows,
commutation, rho1, rho6, G, the classical basis, membership substitutivity,
and even full atomic equality and membership vacuity are valid. Distribution
for raw \(Q\) fails with antecedent bottom and consequent \(\{0\}\).
The native formulas realizing all four values are codes \(0,1,3,44\).
The separate exhaustive four-value checker and receipt are
`check_quantifier_fusion_countermodel.py` and
`quantifier_fusion_countermodel.json`.

This algebra is **not a K model**. In this specific algebra, rho1 forces
equality atoms to \(\{1\}\); substitutivity and membership vacuity then
force membership atoms to bottom, which falsifies K at the true matrix.
Consequently it only refutes a standalone logical-basis equivalence.
Equiconsistency of the full fused-K theory remains open.

There is a useful positive observation. Substituting \(A=B\), generalizing
the tautology \(A\to A\), and applying modus ponens derives commutation.
Consequently each composite \(Q_aQ_b\) is normal; in particular
\(Q'_a=Q_aQ_a\) satisfies distribution. This does not finish an interpretation:
seriality, quantified substitution, commutation of the interpreted operators,
and transport of the exact K matrix/private-code template still require
proofs. Pair normality cannot simply be treated as normality of a single
raw quantifier when moving a commutation implication through an odd prefix.

## 5. A valid gated membership rescheduling, but no state saving

Let

\[
 L(a,b,c)=E(c,a)\to(R(c,b)\to R(a,b)).
\]

Keeping the other original logical rows, it suffices to emit L only when
\(c\ne a,b\). The missing case \(c=a\) is propositional. In the remaining
missing case \(c=b\ne a\), assume \(E(b,a)\) and \(R(b,b)\):

1. Right substitutivity gives \(R(b,a)\).
2. The allowed gated instance \(L(a,a,b)\) gives \(R(a,a)\).
3. Equality symmetry and right substitutivity give \(R(a,b)\).

Thus the row can be conjoined with the existing gated V/K bundle. The former
standalone emitter can produce a duplicate retained axiom, or just native
truth zero, while preserving its stack interface. The common first child of
push macros 166/121/168/177 is a closed 19-primitive block that saves the old
top and leaves new top zero. Zero itself is the literal all-zero instance of
the retained rho8 schema.

The exact words are

```
rho5: [168,166,182,168,121,181,166,121,181,119,119]
rho3: [166,121,182,168,166,181,168,121,181,119,119]
M5:   [168,166,182,168,121,181,168,166,121,181,180,119,119]
```

M5 is the gated quantified version
\(E(c,a)\to(R(c,b)\to Q_cR(a,b))\). With V retained separately, it is
interderivable with gated rho5: V supplies one direction, and the usual
helper elimination (GEN, rho2, seriality, rho6) supplies the other.

Thirty concrete layouts were constructed with direct postfix/AST agreement
and agreement of the two complete CFG resolvers. They included original-row
and original-tree duplication, push-zero replacement, both conjunction
orders, and quantified M5. The best repaired source had 212 distinct DAG
nodes, 4,790 primitive occurrences, and zero run 7, compared with K221's
208/4,744/6. A subsequent bounded closed-rotation search retained 212 nodes
and zero run 7. Every attempted incremental native compilation rejected its
literal decoder binding. These layouts are rejected source experiments,
not verified machines. Mere deletion of the old emitter was not a valid
stack-interface argument and was discarded.

## 6. Other results recorded separately

`theory_findings.md` gives the parametric G-helper equivalence, the already
established admissibility of the eight native constructor binders, the
unsuccessful 223-state implication-binder layout, and a full ordinary model
of the K schema after deleting its support clause. The support-deleted model
uses the natural numbers with membership interpreted as inequality; ZFC
constructs it directly, so that deletion also loses the required strength.

`membership_quantifier_fusion_findings.md` gives the detailed restricted
membership-vacuity countermodels and the exact scopes of those statements.
They show that a canonical binder, even all eight native constructor
binders or a general own-formula-code vacuity family, cannot replace full
fresh membership vacuity by a purely logical argument. Those models do not
claim to satisfy K. The possibility of a genuinely new K-specific
interpretation must be kept separate from those negative logical results.
