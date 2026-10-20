# Further logical fusion attempts

## 1. Canonical membership fusion is valid, but supplies only canonical vacuity

Assume the retained G family and original rho2; its existing proof then gives primitive equality reflexivity. For any native-label builder kappa, replace rho5 by

```
M_kappa(a,b,c) = E(c,a) -> (R(c,b) -> Q_kappa(a,b) R(a,b)).
```

This is exactly derivationally equivalent to rho5 together with the canonical membership helper

```
V_kappa(a,b) = R(a,b) -> Q_kappa(a,b) R(a,b).
```

Indeed, set c=a in M and use E(a,a) to derive V_kappa. Generalize V_kappa at its own binder and use rho2 to obtain `Q_i R(a,b) -> Q_i Q_i R(a,b)`. The retained rho1/rho2/rho6 proof of seriality and double-quantifier elimination gives `Q_i R(a,b) -> R(a,b)`, recovering rho5 from M. The converse is composition of rho5 with V_kappa.

The analogous statement holds for rho3 with

```
E(a,b) -> (R(c,a) -> Q_kappa(c,b) R(c,b)).
```

Setting a=b gives V_kappa(c,b). These are genuine parametric native derivations, not ordinary semantic guesses.

However, canonical membership helpers cannot replace full fresh membership vacuity by the same modular logical argument. The following obstruction is stronger than simply choosing a binder outside kappa's image.

## 2. Finite dependency countermodel for every native constructor helper

Fix any desired binder label z. Let C be the finite set containing z and closed under the two native fields of every positive element n of C: compute (u,v)=P^{-1}(floor(n/4)) and include u and v, regardless of n's residue tag. Treat zero as a terminal label. Both native fields of every positive code are strictly smaller than that code, so this closure is finite. It simultaneously covers all four native constructors, in either argument order.

Let D be the finite set of ordered endpoint pairs (x,y) for which one of

```
4P(x,y), 4P(x,y)+1, 4P(x,y)+2, 4P(x,y)+3
```

belongs to C. Include reversed pairs if reversed-builder helpers are among the proposed axioms. The endpoint labels of every pair in D lie in C, including the possible zero pair.

Use worlds v:N->{0,1,2}, ordinary coordinate-assignment universal quantifiers Q_i, classical implication, and actual value equality `E(a,b)(v) iff v(a)=v(b)`. Define membership by

```
R(a,b)(v) iff
    v(a) != v(b)
    and v(z)=0
    and for every (x,y) in D, (v(a),v(b)) != (v(x),v(y)).
```

For a fixed world this is one genuine relation on the value domain, depending on the finite hidden coordinates C. Thus the ordinary atomic equality-congruence rows rho3/rho5 hold, as do rho7, all equality vacuity, rho1, rho2, rho4, rho6 and the relative-classical bridge. F=R(0,0) is everywhere false. GEN and MP preserve validity. This is a model of the abstract native logical axioms with altered vacuity, not a standard first-order structure with a valuation-independent membership relation; the latter independence is exactly what full membership vacuity would enforce.

For a proposed canonical helper with binder w=kappa(a,b):

* If w is in C, the pair (a,b) is forbidden by D, so its membership atom is identically false and its helper is valid.
* If w is outside C, w is outside every hidden coordinate and outside the two endpoint labels (except the harmless implication-code collision at a=b=w=0, where R(0,0) is false). Its membership atom is therefore independent of coordinate w, so its helper is valid.

This proves simultaneously every atomic helper from all four constructors and both endpoint orders.

Nevertheless choose distinct a,b outside C, set every coordinate in C to zero, and set v(a)=1,v(b)=2. Then R(a,b) is true, since every forbidden value pair is (0,0). Changing v(z) to1 makes it false. Hence

```
R(a,b) -> Q_z R(a,b)
```

fails, with z distinct from both endpoint labels.

This also refutes the hope that restricting logical variables to the image of kappa automatically repairs completeness: z was arbitrary, including labels within that image. The model even validates the stronger general own-code scheme `A -> Q_code(A) A` for every native formula A. If code(A) lies in C, every membership atom appearing in A is identically false because its code and endpoint pair lie in the closure; native code freshness then makes A independent of its own binder. If code(A) lies outside C, that binder is outside the hidden coordinates and outside all ordinary labels of A. Code zero is a separate constant-true case.

Scope: this is a logical non-derivability theorem. It does not model K and does not rule out a new interpretation that uses particular K schema instances to recover a consistency reduction.

## 3. Directly gated membership fusion has a separate obstruction

Consider

```
M_gate(a,b,c) = E(c,a) -> (R(c,b) -> Q_c R(a,b)),   c!=a,b.
```

Use worlds v:N->N and ordinary assignment quantifiers/equality. Define

```
R(a,b)(v) iff a!=b as numerical labels and v is injective.
```

F=R(0,0) is false. All original atomic equality-congruence rows, including BOTH rho3 and rho5, hold: whenever a membership antecedent is true, equality of values forces equality of numerical labels. Full equality vacuity and the remaining pure quantifier/classical schemas hold as well.

Each gated M instance is vacuous: membership truth implies injectivity, while E(c,a) with distinct labels c,a contradicts injectivity. But at the identity valuation, R(a,b) is true for distinct a,b; varying a fresh coordinate c to equal v(a) destroys injectivity. Full fresh membership vacuity therefore fails.

Thus putting the binder directly on the pivot under the existing freshness gate does not repair the canonical-helper gap, even when both old membership substitutivity rows remain.

## 4. A positive gated-placement lemma

Although the fused M_gate fails, the ORIGINAL rho5 itself can be restricted to c!=a,b without losing any native theorem, provided full V is retained and rho3 and primitive equality symmetry remain available.

For the missing pivot case c=a, rho5 is a propositional tautology. For c=b with a!=b, assume E(b,a) and R(b,b):

1. rho3 gives R(b,a).
2. The allowed gated rho5(a,a,b) gives R(a,a), since b differs from both copies of a.
3. Equality symmetry gives E(a,b); rho3 then gives R(a,b).

This proves the omitted rho5(a,b,b). Every other instance was retained. The reasoning can be compiled into finite closed implication proofs using the established classical bridge. Therefore moving rho5 into the bundle as an additional conjunct `rho5 and V and K`, and deleting its ungated stack row, is a valid source-layout experiment. It does NOT justify fusing away the separate V conjunct. No smaller literal table was constructed for this rearrangement.

A genuinely fused four-parameter row would work:

```
E(d,a) -> (R(d,b) -> Q_c R(a,b)),   c!=a,b,
```

with independent pivot d. Choosing d=a yields every full V(a,b,c); generalized helper elimination recovers rho5. The independent fourth parameter is the essential difference from M_gate. Its arithmetic cost must include preservation/reuse of that parameter and appropriate row gating; no state saving is claimed.

## 5. Quantifier distribution/commutation fusion fails

The two proposed four-parameter fusions are

```
Q_a Q_b(P -> R) -> (Q_a Q_b P -> Q_b Q_a R),
Q_a Q_b(P -> R) -> (Q_b Q_a P -> Q_a Q_b R).
```

Both are valid in ordinary first-order semantics and follow from rho2 plus rho4. The converse cannot be obtained from the other retained logical schemas. A four-element Boolean-algebra countermodel already suffices.

Let the Boolean values be 0=empty, A={0}, B={1}, T={0,1}. Every binder uses the same operator

| X | 0 | A | B | T |
|---|---|---|---|---|
| Q(X) | T | 0 | T | T |

Give every membership atom value0 and every equality atom valueB. Implication is ordinary Boolean implication, and F=R(0,0)=0. Then:

* Q squared is constantly T, so BOTH proposed fused rows and rho4 are always T.
* The antecedent Ex(QX) of rho6 is constantly0; rho6 is valid.
* rho1 has value Ex(E)=not Q(not B)=not Q(A)=T.
* All equality-vacuity, membership-vacuity, rho3/rho5/rho7 and merged G instances are valid.
* rho8 is an ordinary implicational tautology; theorem GEN preserves T, and MP preserves validity.

But original rho2 fails at P=F=0 and R=not E(0,0)=A:

```
Q(P->R)=T, QP=T, QR=0.
```

These are actual native formula codes: P=1, R=44, binder0, and the failed rho2 code is 10287019637276668. All four algebra values are attained by native codes: truth0 has valueT, falsity1 has value0, Eq(0,0) code3 has valueB, and its negation code44 has valueA. Consequently this is a countermodel to the native numerical logical calculus, not merely a schema with additional uninterpreted propositional atoms.

The executable independent checker is `check_quantifier_fusion_countermodel.py`; its output is `quantifier_fusion_countermodel.json`. It exhausts all finite algebra values for the schematic formula arguments, while labels are arbitrary because all label operators and atomic assignments are uniform. Its proof scope explicitly excludes K, which is not modeled by this algebra.
