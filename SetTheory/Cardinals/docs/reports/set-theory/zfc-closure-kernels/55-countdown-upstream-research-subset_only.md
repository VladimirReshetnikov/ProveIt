# Subset-only positive seeded closure

New research, 16 October 2026, following [the intake reconciliation](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md).

Deleting the membership arm of source 02's mixed bound preserves its calibration. Extensionality plus subset-only positive point-seeded closure is deductively equivalent to ZF without Foundation and Choice. A subset-seeded version has a direct equality-free calibration with profile congruence. Their totals in source 02's formula-tree metric are respectively 65 and 79 nodes, compared with its mixed-bound totals of 69 and 83. These are formula counts; no new Turing-machine state bound follows.

This answers an open question in source 02 as subsequent research. It does not change the intake's account of what the delivered manuscripts prove. Source 01 supplies the guarded-image, partial-functional-image and singleton-decoding background; source 02 supplies positive seeded closure, exact constant classes, two-cycle Pairing, Russell-root Replacement, and the gated singleton decoder; source 03 develops the gated decoder and exact-fiber hull route. The additional observation here is that a positive decoder hull covers the members of its initial root, even when the root itself is absent from the output hull. That observation lets the decoder recover Separation before Union is available.

The current project target is a fixed binary Turing machine `M`, with fewer than 254 nonhalting states, for which ZFC proves

\[
 \neg\operatorname{Halt}_{\rm blank}(M)
       \ \longleftrightarrow\ \operatorname{Con}(\mathrm{ZFC}).
\]

The result below supplies a smaller candidate theory. It supplies no literal machine, serialized proof translation, or proof of the displayed machine endpoint. Subsequently, [PSCCalibration.lean](../../Lean/BusyBeaver/ZFC/PSCCalibration.lean) checked full first-order deductive equivalence for the equality-bearing subset-seeded variant with `ZF₀`; the point-seeded and equality-free calibrations remain mathematical here. The separate Foundation/Choice consistency bridge is not formalized by that result. The delivered sources' stronger PA claims remain their own mathematical calibration arguments; changing our target metatheory does not create missing certificates.

## The schema and the comparison theory

Work in classical first-order membership logic with logical equality and a nonempty domain. Abbreviate

\[
 x\subseteq b\quad:\Longleftrightarrow\quad
        \forall z\,(z\in x\to z\in b).
\]

Let `ZF₀` consist of Extensionality, Empty Set, Pairing, Union, Power Set, Infinity, full Separation, and functional Replacement. It has neither Foundation nor Choice. Unrestricted Collection is not assumed as an additional schema.

Fix a seed formula `σ(x,a)` with free variables among `x,a`, satisfying two hypotheses:

1. Pure first-order logic proves `∀a σ(a,a)`.
2. `ZF₀` proves `∀a ∃S ∀x (x∈S ↔ σ(x,a))`.

The intended examples are the point seed `σ(x,a) ≡ x=a`, whose seed set is `{a}`, and the subset seed `σ(x,a) ≡ x⊆a`, whose seed set is `P(a)`.

For each formula `ρ(x,y;p̄)`, put

\[
 \operatorname{SB}(\rho):\quad
       \forall x\exists b\forall y\,
                 (\rho(x,y;\bar p)\to y\subseteq b).
\]

The subset-only positive seeded closure schema, denoted `PSCσ`, is

\[
\begin{split}
 \operatorname{SB}(\rho)\longrightarrow\forall a\exists C\,[{}&
  \forall x\forall y\,
   (((\sigma(x,a)\lor x\in C)\land\rho(x,y;\bar p))
                               \to y\in C)\\
 &{}\land\forall y\,(y\in C\to\exists x\,\rho(x,y;\bar p))].
\end{split}
\tag{PSC}
\]

All parameters are universally closed. Matrices have arbitrary finite complexity and arbitrary finite parameter tuples. The seed variable `a`, output witness `C`, and auxiliary bound variables are fresh for the matrix, using capture-avoiding renaming. An intended seed can occur as an ordinary parameter in the matrix; that parameter and the independently bound seed variable may subsequently be instantiated with the same object. The existential input in the final support clause is unrestricted.

**Theorem.** For either intended seed, and more generally every fixed seed satisfying the two hypotheses above, `Extensionality + PSCσ` and `ZF₀` are deductively equivalent by uniform axiom-instance arguments.

The theory still has one fixed nonlogical sentence and one infinite schema. The phrase “for every formula” does not make it a finite first-order axiomatization.

## Exact classes, singletons and Power Set

**Exact-class lemma.** If `∃b ∀y (θ(y;p̄) → y⊆b)`, then there is an `E` with `∀y (y∈E ↔ θ(y;p̄))`.

Use the constant relation `ρ(x,y) ≡ θ(y)`. Its local bound is the assumed bound, at every input. Choose any object `a`, using the nonempty-domain convention. Since `σ(a,a)`, the closure clause puts every `θ`-output into `E`. The support clause gives `y∈E → ∃x θ(y)`, hence the converse implication. This uses no prior Separation or simultaneous selection of bounds.

Three constructions follow immediately:

- `θ(y) ≡ ⊥` gives an empty set, with any bound.
- `θ(y) ≡ y=t` gives `{t}`, with bound `t`, since `t⊆t`.
- `θ(y) ≡ y⊆A` gives the full Power Set of `A`, with bound `A`.

Power Set is recovered here, independently of the transitive decoder below. This preserves the distinction between a `C_T` resource giving transitive closure and a `C_P` resource providing all subsets. A locally subset-bounded fiber may consist of **all** subsets of `A`; the constant relation exposes that entire fiber as a set. With mere membership bounds, asserting that this fiber is bounded would already require the missing Power Set resource. The later decoder obtains transitive covers for Separation and Union; it does not replace the schema's ability to collect subset fibers.

## A transitive positive hull that covers the root's members

Define

\[
 \operatorname{Sing}(x,t):\quad
        \forall z\,(z\in x\leftrightarrow z=t)
\]

and the gated singleton decoder

\[
 \rho_*(x,y):\quad
  \operatorname{Sing}(x,y)\ \lor\
  (\neg\exists t\,\operatorname{Sing}(x,t)\land y\subseteq x).
\]

For each fixed input `x`, reason by cases. If `Sing(x,t)` for some `t`, that `t` is unique: `t∈x` and `Sing(x,u)` imply `t=u`. Every output is therefore `t`, and `b=t` is a subset bound. If `x` is not a singleton, its outputs are exactly the subsets of `x`, bounded by `x`. This proves `SB(ρ*)` through local existence arguments. It does not collect chosen bounds, form a binary union, or combine two possibly incompatible local bounds. The mutually exclusive gate is necessary to this argument.

Apply `(PSC)` to `ρ*` at seed `A`, obtaining `C`.

First, `C` is transitive. Given `x∈C` and `y∈x`, if `x` is a singleton the decoder directly puts `y` in `C`. Otherwise the already available singleton `s={y}` satisfies `s⊆x`. Closure first puts `s` in `C`, and its decoder edge then puts `y` in `C`.

Second, `A⊆C`. Given `y∈A`, if `A` is a singleton, `ρ*(A,y)` and the allowed initial input `A` immediately put `y` in `C`. If `A` is not a singleton, `{y}⊆A`, so the initial input `A` outputs `{y}`; the decoder then outputs `y`. The initial input is allowed because `σ(A,A)` is logically true.

Thus, before Separation or Union has been derived, every `A` has a transitive set `C` with `A⊆C`. The proof does not assume `A∈C`. Indeed, a positive hull need only contain outputs. The support clause is not needed for this particular hull lemma.

## Separation and Union

For Separation on `A` with arbitrary matrix `ψ(y;p̄)`, choose the transitive cover `C` just obtained. If `y∈A`, then `y∈C`; transitivity implies `y⊆C`. Therefore

\[
 \theta(y)\equiv y\in A\land\psi(y;\bar p)
\]

is subset-bounded by `C`. The exact-class lemma gives the required separated set. This proves full Separation, with parameters and arbitrary formula complexity.

For Union of `A`, use the same transitive cover. If `y∈x∈A`, then `x∈C`, then `y∈C`, then `y⊆C`. Consequently

\[
 \theta(y)\equiv\exists x\,(x\in A\land y\in x)
\]

is subset-bounded by `C`. Exact-class formation gives precisely `⋃A`. This proof does not use a previously available Union operation to bound the decoder.

## Pairing, functional Replacement and Infinity

For Pairing of `u,v`, use

\[
 \rho(x,y)\equiv(x=u\land y=v)\lor(x=v\land y=u).
\]

Each input has at most one output, including when `u=v`. A nonempty fiber with sole output `t` is subset-bounded by `t`; an empty fiber has any bound. At seed `u`, the first edge gives `v∈C`; closure then gives `u∈C`. Support implies that every member of `C` equals `u` or `v`, so `C` is their exact pair. No pair bound is assumed in this proof.

For a relation `φ(x,y;p̄)` at most single-valued on `A`, Separation gives

\[
 r=\{t\in A:t\notin t\}.
\]

Russell's argument proves `r∉A`: assuming `r∈A` gives `r∈r ↔ r∉r`. Set `U=⋃A`, now available, and use

\[
 \rho(x,y)\equiv
       (x=r\land y\in A)\lor(x\in A\land\varphi(x,y;\bar p)).
\]

At input `r`, every output belongs to `A`, and therefore is a subset of `U`. At an input in `A`, the first branch is false and there is at most one output, bounded by itself if present. Every other fiber is empty. These cases prove `SB(ρ)` without Collection or Choice.

At seed `r`, all members of `A` enter the positive hull, and closure includes all their `φ`-outputs. Separation in that hull gives the exact partial functional image. In particular, ordinary functional Replacement holds. The subset bound `⋃A` used here is legitimate because Union was proved earlier.

For Infinity, let `e` be empty. Pairing and Union supply each successor `x⁺=x∪{x}`, unique by Extensionality. The relation

\[
 \operatorname{Succ}(x,y):\quad
       \forall z\,(z\in y\leftrightarrow(z\in x\lor z=x))
\]

has one output at each input, subset-bounded by that output. Apply `(PSC)` at seed `e`. The positive hull `C` contains `e⁺` and is successor-closed. It need not contain `e`. Form `I=C∪{e}` using Pairing and Union. Then `e∈I` and every member of `I` has its successor in `I`. This is the ordinary Infinity axiom.

All axioms of `ZF₀` have now been derived. No step assumes Foundation or unrestricted Collection.

## The reverse construction uses unique exact fibers

Work in `ZF₀`, fix `ρ`, and assume `SB(ρ)`. For each fixed input `x`, take a local bound `b` only inside the existence proof. Separation in `P(b)` gives

\[
 d_x=\{y\in\mathcal P(b):\rho(x,y;\bar p)\}.
\]

This is the exact fiber `{y:ρ(x,y;p̄)}`. Extensionality makes it unique and independent of the chosen bound. Thus “`d` is the exact fiber at `x`” is a definable, everywhere functional relation. Functional Replacement may collect those exact fibers without choosing a family of arbitrary bounds.

For a set `D`, form

\[
 F(D)=\bigcup\{d_x:x\in D\}.
\]

For the fixed seed `a`, use its seed-set theorem to obtain `D₀={x:σ(x,a)}`. This is `{a}` for point seeding and `P(a)` for subset seeding. Ordinary recursion on `ω`, available in `ZF₀`, supplies `Dₙ₊₁=F(Dₙ)`. Set

\[
 C=\bigcup_{n<\omega}D_{n+1}.
\]

Every output of an initial seed input lies in `D₁⊆C`. If `x∈C`, it lies in some `Dₙ₊₁`, so all its outputs lie in `Dₙ₊₂⊆C`. Finally, every member of `C` occurs in a positive stage and hence is an output of some input. This proves both clauses of `(PSC)`. The stages need not be increasing; taking the union of all positive stages suffices. Foundation and Choice are not used.

This completes the ordinary mathematical proof of deductive equivalence. The constructions are uniform in the source matrix: fixed proof patterns insert that matrix using fresh variables and capture-avoiding substitution. Turning those patterns into a chosen coded calculus and proving the proof-transformer statements remains a certification task. Composing them with the usual effective Foundation/Choice reductions connects the candidate to ZFC. No exported formalization of that bridge is supplied here.

## Equality-free subset-seeded control

In equality-free membership logic define

\[
 D(x,y):\quad\forall z\,(z\in x\leftrightarrow z\in y)
\]

and retain the profile-congruence sentence

\[
 \mathrm{CG}:\quad\forall x\forall y\,
      (D(x,y)\to\forall w\,(x\in w\leftrightarrow y\in w)).
\]

This is source 02's `EC`, renamed here to `CG` for the common project terminology. Let `QPSC` consist of `CG` and all equality-free subset-seeded `(PSC)` instances with arbitrary equality-free matrices.

Translate equality atoms `x=y` to `D(x,y)` and commute with all other formula constructors. Pure logic makes `D` an equivalence relation. Its definition gives membership congruence in the second argument; `CG` supplies the first argument. Formula induction gives substitution for arbitrary formulas. Translated Extensionality is the logical tautology `∀x∀y(D(x,y)→D(x,y))`. Both the subset seed and the subset-only wrapper are equality-free, so a translated closure instance is a literal allowed instance with the translated matrix. Thus equality-bearing proofs translate to `QPSC` proofs, preserving falsity.

Conversely, Extensionality gives `D(x,y)→x=y`; equality substitution then derives `CG`. Every equality-free closure instance is already an instance of the equality-bearing theory. This gives the reverse falsity-preserving proof expansion. Together with the theorem, it establishes the mathematical equiconsistency calibration of `QPSC` with `ZF₀` and ZFC.

Dropping `CG` is not covered. In particular, the singleton-decoder proof above uses actual equality; its translation is sound because `CG` supplies the substitution law. One cannot discard that hypothesis while retaining the proof.

## The measured saving and remaining machine work

The comparison uses source 02's unchanged formula basis and expansion policy: membership, logical equality, falsity, implication, and universal quantification; each matrix occurrence is one atom. The subset-only point wrapper is already encoded there as the open candidate `PISI_open`. Replacing only the mixed-bound antecedent in its subset-seeded wrapper gives the other new wrapper.

| Template or candidate | Expanded formula-tree nodes |
|---|---:|
| Extensionality | 16 |
| Profile congruence `CG` / source 02 `EC` | 27 |
| Subset-only point wrapper | 49 |
| Subset-only subset wrapper | 52 |
| Extensionality + subset-only point wrapper | **65** |
| Extensionality + subset-only subset wrapper | **68** |
| Equality-free `CG` + subset-only subset wrapper | **79** |
| Delivered mixed-bound point candidate | 69 |
| Delivered mixed-bound subset candidate | 72 |
| Delivered equality-free mixed-bound subset candidate | 83 |
| Inherited RCC control in the same metric | 80 |

Deleting the membership arm saves four expanded nodes in each seeded candidate. The metric excludes variable payloads, arbitrary parameter closure, equality/proof-engine machinery, and backend costs. In particular, the point candidate uses logical equality, while `QPSC` does not. Sharing a subset constructor may matter more to a machine generator than the expanded-tree differences. Actual compilation must decide that comparison.

The next machine experiment should put these candidates through the same certificate calculus, enumeration method, target convention and binary-machine backend. A theoremhood target requires its own falsity-preserving calibration; an off-diagonal atom cannot silently replace falsity inside arbitrary formulas. The final state count must include the complete parser, checker, enumeration, initialization and backend, and the correctness theorem must identify the literal transition table. This note supplies no checker correctness proof, serialized proof compiler, optimality claim, ZFC inconsistency claim, or smaller machine.
