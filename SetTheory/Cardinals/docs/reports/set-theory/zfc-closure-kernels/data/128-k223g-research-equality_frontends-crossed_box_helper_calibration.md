# Double crossed equality helpers: a complete interpretation with no rho7 row

## Proposed logical source change

Retain the exact original rho8 and rho1--rho6 rows, full gated membership
vacuity, modus ponens, and generalization of **closed theorems only**. Delete
rho7 and do not insert primitive equality symmetry. Replace the ordinary
canonical equality helper by

\[
 C^2_\kappa(a,b):\quad
 d_{ab}\longrightarrow\forall_k\forall_k d_{ba},
 \qquad k=\kappa(a,b),\quad a\ne b.
\]

Here `d_ab = Eq(a,b)`. The helper need be supplied only for off-diagonal
pairs. The only condition on the helper function is

\[
 a\ne b\implies \kappa(a,b)\notin\{a,b\}.
\]

It can be the native membership code `RelCode(a,b)`, its argument reversal,
`a+b+1`, or any other computable fresh choice. Alternatively, retain the
original gate `c != a,b` and emit

\[
 d_{ab}\longrightarrow\forall_c\forall_c d_{ba}.
\]

That version supplies all required instances without computing a canonical
binder. These alternatives have the same mathematical calibration; their
compiled state counts are separate empirical questions.

The conclusion is equality **interpretability**, and consequently the same
ordinary syntactic consistency strength as the already calibrated K theory.
It is not a claim that the new system proves every old primitive equality
theorem with its old numerical code.

## 1. Two boxes imply their matrix

Write `Q_i A` for `All(i,A)` and `Ex_i A` for `not Q_i not A`.
The retained rho8/rho6 bridge supplies the ordinary classical propositional consequences,
uniformly in all numerical formula codes. In particular, the designated
bottom remains the exact code `F=Rel(0,0)=1`; no assumption that its raw
variable 0 is syntactically closed is needed.

First derive seriality:

\[
 Q_i A\longrightarrow\operatorname{Ex}_i A.
\]

To see the dependency precisely, use rho1 to obtain
`Ex_i Eq(i,i)`. Generalize the propositional tautology
`A -> (Eq(i,i) -> A)` and apply rho2 to derive
`Q_i A -> Q_i(Eq(i,i) -> A)`. The classical existential consequence of
rho2 gives
`Q_i(Eq(i,i) -> A) -> (Ex_i Eq(i,i) -> Ex_i A)`.
Compose these closed theorems. No equality reflexivity theorem is used.

Apply seriality to `Q_i A`, then use original rho6:

\[
 Q_iQ_i A\longrightarrow\operatorname{Ex}_i Q_i A
 \longrightarrow A. \tag{1}
\]

This is uniform in `A`; it does not assert the generally stronger
`Q_i A -> A` for arbitrary primitive equality-containing formulas.

## 2. Primitive symmetry is derived before any equality interpretation

Compose `C^2_kappa(a,b)` with (1), taking `A=d_ba`:

\[
 d_{ab}\longrightarrow d_{ba}. \tag{2}
\]

For `a=b`, (2) is propositional identity, so no diagonal helper is required.
This establishes primitive symmetry using only the new helper and
rho1, rho2, rho6, the classical propositional bridge, closed GEN, and MP.
In particular, this proof does not depend on equality vacuity, rho7,
universal specialization, or a previously interpreted equality relation.

The order of this argument is useful: once (2) has been established, all
the membership-only certificate constructions in the baseline Source116
indiscernibility module can be reused, with each primitive `SYM` leaf
replaced by this finite derivation.

## 3. Restricted specialization and binder transport

The retained full membership-vacuity family and rho2/rho4/rho6 yield
fresh-vacuity for formulas built from membership, implication, the
designated bottom, and quantifiers. The proof is the existing structural
induction from Source116. It never supplies primitive Eq-vacuity.

Atomic rho3/rho5 and the now derived (2) yield both directions of
quantifier-free membership Leibniz replacement. With rho1 and the
existential consequence of rho2, this proves quantifier-free membership
specialization

\[
 Q_x B\longrightarrow B[y/x]
 \quad(x\ne y).
\]

The last existential is removed using membership-only fresh vacuity and
rho6. Self-specialization

\[
 Q_x B\longrightarrow B \tag{3}
\]

follows by choosing a fresh auxiliary `y`, specializing from `x` to `y`,
using vacuity to generalize at `y`, and specializing back. Both parts are
closed theorem constructions. As in the baseline certificate API, a
designated bottom is fixed by this auxiliary renaming operation; this is
not a general raw-syntax substitution theorem.

Let

\[
\begin{aligned}
 B^-_{ab}(z)&=(R(z,a)\to R(z,b))\wedge(R(z,b)\to R(z,a)),\\
 B^+_{ab}(z)&=(R(a,z)\to R(b,z))\wedge(R(b,z)\to R(a,z)),\\
 E^z(a,b)&=Q_zB^-_{ab}(z)\wedge Q_zB^+_{ab}(z),\qquad z\notin\{a,b\},\\
 E(a,b)&=E^{e(a,b)}(a,b),\qquad e(a,b)=\operatorname{EqCode}(a,b).
\end{aligned}
\]

The negative conjunction expansion is exactly the baseline expansion
`A and B = not(A -> not B)`. Since the native Eq code exceeds both endpoint
labels, `E` uses a fixed safe internal auxiliary for each pair.

Quantifier-free specialization and membership-only vacuity prove

\[
 E^z(a,b)\leftrightarrow E^w(a,b)
\]

whenever both auxiliary labels are safe. This is the existing explicit
Source116 safe auxiliary transport; primitive Eq-vacuity is not a
dependency. Neither the computed binder nor this transport is assumed to
commute with arbitrary syntactic substitution.

## 4. The new helper implies membership indiscernibility

Fix distinct `a,b`, and write `k=kappa(a,b)`. By (2) and rho3/rho5,

\[
 d_{ba}\longrightarrow B^-_{ab}(k),\qquad
 d_{ba}\longrightarrow B^+_{ab}(k).
\]

Double generalization of each closed implication, followed by rho2,
gives `Q_k Q_k d_ba -> Q_k Q_k B` for the relevant body `B`.
The new helper therefore gives

\[
 d_{ab}\longrightarrow Q_k Q_k B.
\]

The quantifier-free self-specialization theorem (3) can itself be
generalized at `k`. Rho2 then gives

\[
 Q_k Q_k B\longrightarrow Q_k B.
\]

Combine the inward and outward bodies to obtain

\[
 d_{ab}\longrightarrow E^k(a,b)\longrightarrow E(a,b). \tag{4}
\]

For `a=b`, `E(a,a)` follows directly by generalizing membership identity
tautologies. Thus (4) also holds on the diagonal without any diagonal C2
instance. Existential monotonicity and rho1 now yield

\[
 \operatorname{Ex}_a E(a,b). \tag{5}
\]

There is no circularity: seriality and (1) come first, then primitive
symmetry, then membership-only specialization, and finally (4) and (5).

## 5. Completion of the comparison-calculus interpretation

Using the exact same safe-auxiliary construction as Source116, membership
indiscernibility satisfies:

* The translated rho3/rho5 membership congruence laws, including a third
  label that equals the fixed internal auxiliary.
* The translated rho7 Euclidean law, by transporting three equality
  relations to a common fresh auxiliary and combining propositional
  membership equivalences.
* Every gated equality-vacuity instance, including quantification at the
  fixed internal auxiliary and at label 0.
* The translated rho1 existence law (5).

The interpretation fixes membership, implication, and quantifiers and
replaces primitive Eq with `E`. It commutes with MP and closed GEN by
definition. The original rho1--rho8 calculus is therefore interpreted in
the new source theory, even though its primitive rho7 row is absent.

For the unchanged K source, the existing native-matrix/code-coupling
adapter from `k_equality_helper_extension.md` still applies. In particular,
the comparison K private label is chosen **after** interpreting the
membership matrix, and the already documented double-negation padding
provides the required native freshness and literal code identity. This
proof supplies a new equality bootstrap; it does not alter that K adapter.

The converse consistency direction is immediate from the original
ordinary model interpretation: standard equality makes each off-diagonal
C2 helper true because its binder is fresh from both endpoints. Thus the
same calibrated K theory and the C2 variant have equivalent ordinary
syntactic consistency statements. The finite proof transformations and
the retained ordinary K-to-ZFC calibration can be formalized in ZFC.
This is not a newly implemented kernel theorem for the changed binary
transition table.

## 6. Source coverage freedom

The C2 helper is needed only off the diagonal. Consequently, under the
original gate `c != a,b`, the helper's ordered endpoint roles may be
`(a,b)`, `(b,a)`, `(a,c)`, `(c,a)`, `(b,c)`, or `(c,b)`, provided the binder
is fresh from the selected endpoints. For an endpoint pair involving `c`,
the unused parameter can always be chosen distinct from `c`, so all
off-diagonal pairs are emitted. Diagonal instances need not be recovered.
This freedom should be used when searching the actual continuation-sharing
DAG; shorter expanded source expressions alone do not establish a smaller
state count.

## 7. Reproducible finite certificates

`crossed_box_helper_certificate.py` builds closed derivation DAGs, checks
all leaves and all MP/GEN nodes, writes JSON, reloads the JSON, and checks
it again. It depends only on Python's standard library and the bundled
`combined_helper_certificate.py` representation/export module. Run:

```
python crossed_box_helper_certificate.py --kappa rel
python crossed_box_helper_certificate.py --kappa sum
```

The roots cover primitive symmetry, Eq-to-E, translated existence,
internal-binder vacuity, membership congruence with label 0 and the
internal auxiliary, and translated rho7 with coincident endpoints.
Every C2 leaf is off-diagonal and checked against the selected actual
numeric helper function. `SYM`, Eq-vacuity, rho7, general substitution,
and alpha-conversion are all rejected as proof leaves.

These certificates test concrete instantiations of the uniform
construction above. The Boolean TAUT leaf convention has exactly the
unchanged rho8 dependency used by the baseline; the certificate is not a
replacement for a Rocq/Lean kernel proof of that pre-existing bridge.
