# A full ZFC-constructible countermodel to the native T replacement

## Result and scope

Let the current numerical seed-K calculus retain every original row and rule except that

\[
\rho_6(i,A):\quad (\exists_i Q_iA)\to A
\]

is replaced by either

\[
T(i,A):Q_iA\to A,
\qquad\text{or}\qquad
B^\vee(i,A):A\to Q_i\exists_i A.
\]

**ZFC proves the consistency of either modified numerical calculus.** The second statement concerns the literal native replacement, where negation is implication to the numerical formula `F=R(0,0)`, not a calculus already supplied with an independent falsity axiom. Consequently, assuming ZFC is consistent, neither modified calculus can have its consistency provably equivalent in ZFC to `Con(ZFC)`.

The construction below is a set-sized, two-world interpretation built inside ZFC. All axiom instances are valid at both worlds and at all assignments, and both inference rules preserve that validity. The target `F` is false at the first world. This is enough to prove that no finite derivation reaches `F`. **The target is true at the second world.** Requiring it to be false at every world would exclude legitimate soundness countermodels and miss the mechanism of this result.

The earlier two-world countermodel using an assumed ordinary K+IR model established only nonderivability of raw rho6. The present construction does not assume an ordinary K+IR model or `Con(ZFC)`, and therefore settles the consistency-strength question for these two literal replacements.

## Why the native bottom matters

The retained file `k225-formal/rocq224/src/Prop222.v`, at ProveIt commit
`9288593a769fa85adeebd2b505edf5c16728ce8f`, proves

```
thm_F a : thm222 (wim 1 a)
```

from rho6: propositional logic gives `F -> Ex_0 Q_0 a`, and rho6 then gives `F -> a`. Double-negation elimination and the full classical negation bridge are subsequently derived using that explosion lemma. The four-variable Lukasiewicz implication row alone treats `F` as another atom and does not supply explosion.

Thus the familiar equivalence between the modal B presentations `diamond box A -> A` and `A -> box diamond A` cannot be invoked before checking this native bridge. They are equivalent with genuine Boolean falsity, but the literal replacement can lose the axiom that makes native `F` act as falsity.

## 1. The domain and modal interpretation

Work inside ZFC. Let

\[
D=H_{\omega_1}=\{x:\operatorname{tc}(\{x\})\text{ is countable}\}
\]

be the set of hereditarily countable sets. We use only these elementary properties:

1. `D` is a nonempty transitive set.
2. Every element of `D` is countable.
3. Every countable set of elements of `D` belongs to `D`.

For the third property, the transitive closure of a countable collection of hereditarily countable sets is a countable union of countable sets. Choice is available in the ambient ZFC. The standard identification with `H_{omega_1}` supplies a set-sized domain; no model of ZFC inside `D` is asserted or required.

There are two times `0 <= 1`. An assignment is a function `v : N -> D`. Interpret implication as ordinary Boolean implication at each time. Code zero is true. Interpret equality as actual identity at both times, and membership by

\[
R_0(x,y)\iff x\in y,
\qquad
R_1(x,y)\iff x\in y\ \lor\ x=y.
\]

For every variable label `i`, put

\[
(Q_iA)(t,v)\iff
\text{for every }s\ge t\text{ and every }d\in D,
A(s,v[i:=d]).
\]

The common time modality and ordinary coordinate quantifiers commute, so these operators are normal, reflexive, and pairwise commuting. We do not infer those properties from an unproved representation of the native calculus: they follow directly from this explicitly defined model.

Foundation in the ambient ZFC gives `x notin x`. Hence the native target has values

\[
F(0,v)=\bot,\qquad F(1,v)=\top
\]

for every assignment. Therefore native negation and existential quantification obey the exact identities

\[
(NA)(0,v)=\neg A(0,v),\qquad(NA)(1,v)=\top,
\]

\[
(\exists_i A)(0,v)\iff\exists d\in D\ A(0,v[i:=d]),
\qquad
(\exists_i A)(1,v)=\top.
\tag{1}
\]

These identities use the literal definitions `NA=I(A,F)` and `Ex_i A=N(Q_i N(A))`. In particular, the native existential at time zero does not choose the second time: its inner negation is automatically true there.

## 2. All retained logical rows and both replacements are valid

The Lukasiewicz row is a classical implicational tautology at each world. Normality and commutation are properties of the displayed `Q_i` operators. The theorem-generalization rule preserves validity because its premise is valid at every time and assignment; modus ponens plainly preserves validity.

Native truth zero is valid, including every gate-failure branch that emits zero. Irreflexivity in the relative form `R(a,a) -> F` is valid as well: both atoms are false at time zero and true at time one. If an irreflexivity presentation instead uses the rule `R(a,a) |- F`, that rule also preserves global validity, since its premise is never globally valid in this interpretation. Thus adding either such IR presentation does not invalidate the countermodel.

Equality existence holds at time zero by ordinary assignment variation: choose the `i` coordinate to equal the value of the target coordinate. When the two labels coincide, reflexive identity already holds. At time one every native existential is true by (1).

Both membership-substitution rows hold because equality is actual identity and, at each fixed time, membership is one relation on values. The merged equality row

\[
E(c,a)\to\bigl(E(c,b)\to Q_{R(a,b)}E(a,b)\bigr)
\]

holds because its antecedents imply equality of the values at `a,b`, and the numerical binder `R(a,b)=4P(a,b)+1` is distinct from both endpoints. Equality is unchanged between times. The diagonal case is harmless even without freshness, since `E(a,a)` is always true.

If `c` differs from `a,b`, fresh membership vacuity holds: changing coordinate `c` does not affect either endpoint, and the membership relation only grows from time zero to time one. Thus

\[
R(a,b)\to Q_cR(a,b)
\]

is valid at both times.

The T replacement is valid by reflexivity of the semantic quantifiers. The dual-B replacement is also valid. At time one its consequent is true by (1). At time zero,

\[
(Q_i\exists_i A)(0,v)
\iff \exists d\in D\ A(0,v[i:=d]),
\]

because the inner existential removes dependence on the `i` coordinate, and its time-one value is true. This follows from `A(0,v)` by choosing `d=v_i`.

The original rho6 is not valid. At time one its antecedent is always true, whereas its consequent can be false, for example an equality atom evaluated at two distinct values of `D`. The same assignment refutes `F -> A`. This locates the exact native bootstrap lost in either replacement.

## 3. Reduction of the literal K template

Fix enabled input/output labels `a,b` and private label `c`, with `c != a,b`. Let `chi` be the decoded matrix whose actual native code is `c`. Every label occurring in the decoded matrix is smaller than its positive code, with the code-zero truth exception; in particular `c` does not occur in `chi`. Thus changing the prospective container coordinate `c` does not change matrix truth at either time.

Use the exact source abbreviations

\[
r=R(b,c),\qquad s=Q_c(R(c,a)\to R(c,b)),
\]

\[
w=Q_b\bigl(\chi\to NQ_b(\chi\to Nr)\bigr),
\qquad u=Q_a(s\to w),
\]

\[
h=Q_b\bigl(r\to NQ_a(\chi\to Nu)\bigr),
\qquad v=R(a,b)\to Q_cR(a,b).
\]

The emitted bundle is

\[
N\bigl(v\to Q_c(h\to Nw)\bigr).
\tag{2}
\]

At time one, `w,u,h` are all true: each decisive native negation is true, and the implications under their quantifiers therefore are true. Also `v` is true. Formula (2) is true because its outer native negation is true.

At time zero, `v` is true. Moreover `(h -> Nw)` is true at time one. Consequently (2) holds exactly when there is a **current-time** container `C in D` for which `h` and `w` hold at time zero.

The time-zero value of the subset test is

\[
\operatorname{Sub}^*(p,z)
\iff p\subseteq z\ \land\ (p=z\ \lor\ p\in z).
\tag{3}
\]

Indeed its first-time universal condition says `p subseteq z`; its second-time condition is

\[
\forall x\in D\bigl[(x\in p\lor x=p)\to(x\in z\lor x=z)\bigr].
\]

Using `x=p` gives `p in z or p=z`; that condition together with `p subseteq z` also suffices. Transitivity of `D` means the quantifier over `D` checks all actual members of `p`.

### Distinct input and output labels

For `a != b`, fix the remaining parameters and write

\[
\varphi(y,p)\iff \chi(0,v[a:=p,b:=y]).
\]

The time-zero K requirement is exactly the ordinary seed template

\[
W_\varphi(p,C)=
(\exists y\in D\,\varphi(y,p))\to
\exists y\in C\,\varphi(y,p),
\]

\[
H^*_\varphi(C)=
\forall z\in C\left[
(\exists p\in D\,\varphi(z,p))\ \land\
\forall p\in D\bigl(\operatorname{Sub}^*(p,z)\to W_\varphi(p,C)\bigr)
\right],
\]

with the request `W_phi(v_a,C)` at the original seed. This reduction follows literally from (1), the truth of `w,u,h` at the second time, and the displayed source template. The support witness is outside the second input quantifier, as in the original emitted formula; the latter overwrites the former input value and therefore makes the universal request conjunct independent of the particular support witness.

The relation `varphi` need not be quantifier-free, monotone, or ordinary-membership definable by any bounded formula. It is the truth relation of an arbitrary finite native matrix in a set-sized structure, hence a set relation available inside ZFC. The next argument works for **every** relation on `D x D`.

## 4. Countable witness closure proves all distinct-label instances

Let `varphi` be any relation on `D x D`, and fix a seed `p0 in D`. Put

\[
P_\varphi=\{p\in D:\exists y\in D\,\varphi(y,p)\}.
\]

By choice, select a function `f : P_phi -> D` such that `varphi(f(p),p)` for every `p` in its domain. Set

\[
C_0=\begin{cases}\{f(p_0)\},&p_0\in P_\varphi,\\
\varnothing,&p_0\notin P_\varphi,
\end{cases}
\]

\[
C_{n+1}=C_n\cup
\{f(p):\exists z\in C_n\ [p\in P_\varphi\land\operatorname{Sub}^*(p,z)]\},
\qquad C=\bigcup_{n<\omega}C_n.
\]

Every request generated by an element `z` is an element of `z union {z}`, by (3). That is a countable collection. Inductively each `C_n` is countable, and then `C` is countable. Every output belongs to `D`, so property 3 of `D` gives `C in D`.

The seed request holds by the definition of `C_0`. Every member of `C` was selected as `f(p)` for some supported input `p`, so the support conjunct holds. Finally, if `z in C` and `Sub*(p,z)`, choose a stage containing `z`. If the fiber at `p` is nonempty, `f(p)` appears at the next stage and witnesses the required request; otherwise that request is vacuous. Therefore `H*_phi(C)` holds.

The ordinary K closure can require witnesses for all subsets of an element. Here the reflexive-closure world changes that test to (3), leaving only countably many possible requests per element. This is precisely why the ambient ZFC can construct all the containers inside the one set `H_{omega_1}`.

## 5. Coincident input and output labels

The literal source also permits `a=b`; only the private-label gate excludes collisions with `c`. This case must not be handled by silently renaming one of the two coincident roles.

Write `psi(x)` for the time-zero matrix truth when the one shared coordinate has value `x`. Then `w` is independent of its incoming shared-coordinate value and is equivalent to

\[
(\exists x\in D\,\psi(x))\to\exists x\in C\,\psi(x).
\]

Inside `u`, the input quantifier also resets the output coordinate, so the subset test has equal endpoints and is true. Thus `u` is equivalent to this same request. The support clause in `h` only asks for some `psi` witness together with that request.

If no `psi` witness exists, choose `C=emptyset`. Otherwise choose one witness `d` and take `C={d}`. These containers belong to `D`; the request and support conditions hold directly. This proves every coincident-label instance as emitted.

The argument also covers low matrix codes, including private code zero (the true matrix) and private code one (the matrix with time-zero value false). No matrix code or permitted role assignment is omitted.

## 6. Internal consequence

The set `D`, the two-world assignment space, the recursive truth definition for native formula codes, and the induction on finite numerical derivations are all available in ZFC. Sections 2–5 establish every axiom instance uniformly. Since `F` is false at time zero under every assignment, soundness proves that no finite derivation reaches `F`.

Hence ZFC proves `Con(K_T)` and `Con(K_dualB)` for the literal modified native proof systems. If ZFC also proved either of these consistency statements equivalent to its own consistency, it would prove `Con(ZFC)`. The second incompleteness theorem rules that out if ZFC is consistent, under the usual effective coding of its proof predicate.

This does not obstruct a different formalism that explicitly restores falsity/explosion and then uses a shorter quantifier presentation. It does rule out accepting the tested T source or the raw dual-B source merely because ordinary first-order specialization or ordinary Boolean modal duality is valid.

## Supplementary executable audit

`check_t_countermodel_reduction.py` independently evaluates the literal displayed K tree on all two-element irreflexive membership relations and arbitrary time-zero/time-one matrix truth tables. It checks the modal-to-ordinary reductions, both role-collision patterns, the true second-time bundle, and the old-rho6 counterinstance. This finite audit is supplementary: the all-formula, all-parameter proof and the hereditary-countability closure argument above establish the unbounded result.
