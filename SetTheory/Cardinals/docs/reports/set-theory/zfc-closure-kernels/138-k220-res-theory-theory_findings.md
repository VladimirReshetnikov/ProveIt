# Independent theory-side investigation

Research context: ProveIt commit c011e44b; K221 source from `K221_Construction_2026-10-20.zip`.

## 1. A uniform merged-equality theorem

Let `I`, `R`, `Q`, `E` be the actual base-four native constructors, `F=R(0,0)=1`, `N(A)=I(A,F)`, and `Ex_i A=N(Q(i,N(A)))`. Retain the original relative-classical bridge (`rho8`, `rho6`), `rho1`, `rho2`, closed-theorem GEN, and MP. For **any** total native-label builder kappa, let

```
H_kappa(a,b) = E(a,b) -> Q_kappa(a,b) E(a,b)
G_kappa(a,b,c) = E(c,a) -> (E(c,b) -> Q_kappa(a,b) E(a,b)).
```

Here `Q_kappa(a,b)` denotes the binder label kappa(a,b), not an additional formula argument. The ungated G_kappa family is derivationally equivalent to old rho7 plus H_kappa. No freshness or distinctness assumption is used in this equivalence.

Proof:

1. Closed quantifier/existential monotonicity follows from rho2, GEN and propositional logic. From rho1(i,i), which is `Ex_i E(i,i)`, existential modus ponens yields seriality `Q_i A -> Ex_i A`.
2. Seriality with A replaced by Q_i A and rho6 yield `Q_i Q_i A -> A`.
3. Put z=kappa(x,x), e=E(x,x). Contract G_kappa(x,x,z) to `E(z,x) -> Q_z e`. Lift existentially, use rho1(z,x), then rho6(z,e). This gives e, including when z=x=0.
4. G_kappa(a,b,a) and E(a,a) yield H_kappa(a,b).
5. Generalize H_kappa(a,b) at i=kappa(a,b) and use rho2. This yields `Q_i E(a,b) -> Q_i Q_i E(a,b)`, hence `Q_i E(a,b) -> E(a,b)` by step 2. Compose with G_kappa to recover old rho7.
6. Conversely old rho7 followed by H_kappa yields G_kappa.

If H_kappa was a conjunct of a bundle gated by c!=a,b, it remains uniformly available by taking c=max(a,b)+1. The argument treats every other bundle conjunct as opaque. Thus it applies equally to calibrated output-root, conditional-root, and witness-request K.

For **ZFC calibration**, separately require only

```
a != b implies kappa(a,b) not in {a,b}.
```

No diagonal restriction is necessary. This precise theorem and the native actual-code coupling are ALREADY proved in the vendored predecessor, not a new claim of priority:

- `baseline224/K224_Construction_2026-10-20/portable/theory/source116/proofs/general_kappa_equality_helper.md`
- `baseline224/K224_Construction_2026-10-20/portable/theory/k_equality_helper_extension.md`

They retain membership vacuity and translate primitive equality to bidirectional membership indiscernibility with safe auxiliary `EqCode(a,b)`. Off diagonal H_kappa supplies the Eq-to-indiscernibility bridge; diagonal interpreted equality is a theorem without H. Choose the private K label **after** translating and padding the matrix, as its actual native code. That order prevents the matrix/private-label coupling gap.

### Measured source experiment

The choice kappa(a,b)=I(a,b)=4P(a,b) satisfies the required condition. It exceeds both labels except at (0,0); that diagonal collision is explicitly allowed by the existing theorem.

Replacing R(a,b) by I(a,b) in G deletes precisely the primitive `CI 1` at ordinal 729 in the unchanged 4,744-instruction K221 sequence. The resulting source is `sites_gimp221.json`. Both independent CFG resolvers agree, and all remaining effects and targets equal deletion/reindexing of that one increment:

- 4,743 primitive occurrences, 6,166 guarded cases;
- maximum address depth 38, maximum zero run six;
- 209 distinct subtrees rather than 208 (186 internal rather than185).

The root agent's subsequent literal incremental allocation gives 223 states, two fresh labels, 17 reused labels, twelve contextual aliases. This is a calibrated logical variant and a correctly bound decoder experiment, **not** a verified improvement; no final primitive runtime audit was run. Removing one arithmetic instruction need not reduce the finite-control state count because sharing and source tags change.

## 2. Rigorous obstruction to deleting K support

Consider the tempting weaker seed schema formed by dropping the support requirement from H:

```
Sub(p,u) := forall z (R(z,p) -> R(z,u)).
W_phi(p,C) := (exists y phi(y,p,q)) -> exists y (phi(y,p,q) and R(y,C)).
H^-_phi(C) := forall u (R(u,C) -> forall p (Sub(p,u) -> W_phi(p,C))).
forall a exists C (W_phi(a,C) and H^-_phi(C)).
```

This theory with genuine equality and irreflexivity has an explicit countably infinite model: domain N with `R(x,y) iff x!=y`.

First, `Sub(p,u)` holds exactly when p=u. If p!=u, choose z=u: R(u,p) is true while R(u,u) is false. The converse is immediate.

Fix an arbitrary formula phi in this equality-and-R language, any finite tuple of parameters q, and seed a. Choose C outside the finite set of values named by a,q. Whenever p!=C and an output witness y exists, a witness other than C exists. If the original witness is already different from C, use it. If it is C, choose d outside the finite set {C,p,q}; the permutation exchanging C,d and fixing all other elements is an automorphism of the structure fixing p,q. It carries phi(C,p,q) to phi(d,p,q). Thus W_phi(p,C) holds for every p!=C. It applies to the seed a, and also to every u with R(u,C), since Sub(p,u) forces p=u!=C. Hence the entire schema holds.

The argument covers every first-order formula, not just quantifier-free matrices or finite examples. The original K support conjunct `exists p phi(u,p,q)` is therefore essential to rule out this particular trivial co-membership model. One cannot remove it and inherit K's ZFC calibration. Indeed the weak theory has a straightforward model construction in ordinary weak mathematics with an infinite set; its consistency cannot serve as an equivalent presentation of Con(ZFC) under the intended finite-proof reductions.

Scope: the last conclusion is about this exact deletion. It does not prove that every alternative support condition or equality-free K presentation fails.

## 3. Rigorous obstruction to gated G with binder equal to the pivot

A proposed arithmetic saving moves G into the gate c!=a,b and uses c itself as the binder:

```
G_gate(a,b,c) = E(c,a) -> (E(c,b) -> Q_c E(a,b)),  c!=a,b.
```

This does NOT give the same modular logical calibration as ungated G. The following modal interpretation refutes that equivalence. Worlds are N; each Q_i is the universal modality on N; F is false; every membership atom is false; equality atoms denote

```
E(a,a) = N;
E(a,b) = {b}, a!=b.
```

Interpret implications classically at each world. GEN preserves validity. The original rho2 distribution, rho4 interchange and rho6 `Ex_i Q_i A -> A` hold for the universal modality. Every rho1 `Ex_i E(i,b)` is true because the equality set is nonempty. Both membership-congruence rows and membership vacuity hold because every membership atom is false. The relative-classical bridge also holds.

For a gated G instance, c differs from a,b. If a!=b its two antecedent sets {a} and {b} are disjoint. If a=b its consequent is Q_c E(a,a)=true. Thus every gated G instance is valid.

Nevertheless old rho7 fails for a!=b with pivot c=b at world a: E(b,a) and E(b,b) hold while E(a,b) does not. Every off-diagonal helper `E(a,b) -> Q_k E(a,b)` also fails at world b.

This countermodel concerns the purely logical schemas, with an arbitrary set-theoretic core treated as opaque. It does NOT itself model K, and it does not rule out a more elaborate argument exploiting particular K instances. It shows precisely why the existing opaque-core G equivalence cannot simply be reused after imposing this gate.

## 4. Proof-scope cautions

The pinned K230 Rocq endpoint is an external axiom-free theorem, not by itself an internal ZFC/PA proof. The inherited reports supply ordinary finite-proof transformations and explicit machine-simulation arguments formalizable in ZFC. For a new literal table, an all-parameter runtime certificate plus full blank bootstrap and exact source equivalence supports transport of that ordinary endpoint. It should not be called a newly compiled Rocq or Lean endpoint unless that endpoint was actually compiled and audited.

The proof-search target has a finite derivation if and only if the binary TM eventually halts. No finite simulation can prove unbounded nonhalting. A structural finite certificate can prove a uniform step simulation; these are different uses of finiteness.
