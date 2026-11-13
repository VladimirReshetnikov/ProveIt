# Independent mathematical audit: finite parameters in the numbering theory

Review provenance: this is a separate AI subagent's review of the written proof within this investigation. It is not external peer review or a proof-assistant certificate.

## Scope and conclusion

This review concerns the final three-fiber construction with all numbering laws, fixed-point preservation, and the exceptional update `H*` described below. It supersedes preliminary reviews of weaker constructions.

The inspected comparison source is ProveIt commit `798856e4ef2d02b7f9c0f1660828c5ce58f277f2`, especially `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/Article/chapters/ch10_obs.tex`, subsection “Numeral induction, numbering and fusion” and the named further question “Parameters for the numbering theory.” The review also considered the two current incoming coverage-obstruction papers.

**Assessment:** the final construction proves the claimed finite-parameter obstruction. The prescribed path families are compatible, the general equivariant choice exists, the staged term semantics is coherent and extensional, and the parameter-free literal-equation counterexample is valid. The result answers the named parameter question for the existing theory `T_cal`; it is not a smaller positive axiomatization or a proof-checker complexity lower bound. This is a review of a written mathematical argument, not Lean or Rocq verification.

## Exact claim reviewed

Let `B` be intuitionistic first-order logic with actual equality, zero, successor and the scalar iterator, with the two computation schemas, numerical coverage and `0 != S(0)`. Let `T_num` add successor injectivity and contextual induction for equations `t(n,p) = k`, where each target `k` is one fixed standard numeral. The existing numbering theory is

`T_cal = T_num + Id + {N_k : k is a standard natural number} + Ext`,

where

- `Id`: `I(n,a;u.u) = a`;
- `N_k`: `I(n,k;u.S(u)) = S^k(n)`;
- `Ext`: pointwise equality of two update bodies implies equality of their iterations at the same count and seed.

The new model satisfies `T_cal` and the additional fixed-point scheme

`h(a) = a -> I(n,a;u.h(u)) = a`.

For every finite parameter tuple in that model, a nonidentity involution fixes the tuple. Consequently no ordinary bi-interpretation with iPRA can have its interpretations and definable return isomorphism realized there, even with finite-dimensional definable domains and quotient equality. In particular this excludes a theory-level bi-interpretation whose finite-parameter conditions are proved inhabited.

The same model validates induction for the additional constant-target fragment described below and refutes one explicit instance of literal-equation induction.

## Three fibers and independent involutions

Start with a nonstandard model `M` of PA, definitionally expanded by all primitive recursive functions. Over each standard numeral use a singleton fiber; over every nonstandard element use labels `0,1,2`. The carrier is

`D = {(m,j) : m in M, j=0 if m is standard, j in {0,1,2} otherwise}`.

Projection is `pi(m,j)=m`; zero is `(0,0)`; successor is `S_D(m,j)=(S_M(m),j)`. Thus zero is separated from its successor, successor is injective, and coverage holds.

For every nonstandard successor chain `C` of `M`, independently swap labels `1` and `2` over `C`, fixing label `0` and all other chains. These flips generate the direct sum `G` of copies of the two-element group. They preserve projection, zero and successor.

There are infinitely many nonstandard successor chains: for a nonstandard positive `b`, the chains of `b,2b,3b,...` are distinct. A finite tuple occupies only finitely many chains. Therefore some nontrivial chain flip fixes the tuple. The remaining task is to make every iterator operation equivariant under all of `G`.

## General equivariant path selection

An admissible update is an actual function `h:D->D` whose projection is a unary primitive recursive function with parameters `f:M->M`. For fixed seed `a`, update `h`, and a nonstandard successor chain `X` in `D`, a path must have projection

`pi(p(n)) = It_f(pi(n),pi(a))`

and satisfy `p(S_D(n)) = h(p(n))`.

Let `H` be the stabilizer of the datum `(a,h,X)`. Because the group never changes first coordinates, any group element preserving `X` setwise fixes it pointwise. Hence `H` fixes every point of `X`, fixes `a`, and commutes with `h`.

Intersect each required projected fiber with the fixed-point set of `H`. Every resulting set is finite and nonempty because label `0` is fixed by the entire group. The update `h` maps each such set into the next: projection gives the correct first coordinate and commutation with `H` gives fixedness. A compatible bi-infinite path exists by compactness of the product of finite sets; every finite set of adjacent path equations is satisfied by choosing a value at its least index and propagating forward.

Choose one stabilizer-fixed path for each orbit of data and transport it by the group. This transport is well defined: two transporters differ by a stabilizer, which fixes both the original path domain and every value. Therefore

`I(g(n),g(a),g h g^-1) = g(I(n,a,h))`.

This resolves a real issue absent from the earlier global-involution construction: the larger group has data with nontrivial stabilizers, so freely choosing paths and then transporting them would not suffice. The distinguished fixed label supplies the necessary stabilizer-fixed choices.

## Audit of all three prescribed families

The following invariant families can be fixed before choosing the remaining data orbits.

### Fixed-point preservation

If `h(a)=a`, choose the constant path `p(n)=a`. Its projection is correct because `f(pi(a))=pi(a)` and PA proves that all projected iterates remain at that value. The datum stabilizer fixes `a`. The fixed-point condition and the prescribed path are preserved by conjugation. Together with ordinary finite iteration at standard counts, this gives every fixed-point instance and therefore `Id`.

### Every numbering law

For `h=S_D` and seed the standard numeral `k`, choose `p(n)=S_D^k(n)` on every nonstandard chain. Its projection is

`S_M^k(pi(n)) = It_{S_M}(pi(n),k)`.

The successor recurrence holds. The stabilizer fixes `n` and commutes with successor, hence fixes `S_D^k(n)`. Equivariance follows from the same commutation. Standard-count finite iteration satisfies the same equation, so every `N_k` holds on all of `D`.

These paths preserve the counter's label. The earlier collapsing prescription `(pi(n),0)` for successor from zero must not be retained: it would violate `N_0`.

### The exceptional update giving a literal-equation counterexample

Define the actual update `H*` by `H*(0_D)=2_D` and `H*(x)=S_D(x)` for `x != 0_D`. It is represented by the scalar term

`h(u) = S(C(u,1,u))`, where `C(v,a,b)=I(v,a;w.b)`.

This term representation is independent of unspecified path choices. Computation gives `C(0,a,b)=a` and `C(S(v),a,b)=b`; coverage gives its value at every element. Thus `h(0)=2` and `h(S(v))=S(S(v))` exactly as stated.

For update `H*`, seed `0_D`, and a nonstandard counter, prescribe

`p(n)=(pi(n)+1,0)`.

Its projected update is the primitive recursive function `f(0)=2`, `f(m+1)=m+2`. PA proves that iteration from zero at any positive count `m` is `m+1`, so the projected fiber is correct. The displayed path obeys the successor recurrence. Label `0` makes it fixed by every stabilizer and equivariant under `G`.

All three families are pairwise compatible. `S_D` has no fixed point; `H*` has no fixed point; and `H*` differs from `S_D` at zero. Standard numeral seeds in the numbering family are distinct. Each prescribed family is a union of complete `G`-orbits of data. There is consequently no conflict with the remaining orbit-by-orbit selection.

## Coherent term semantics and extensionality

The iterator is chosen on actual update functions before interpreting finite terms. Structural induction then shows that every term projects to its ordinary primitive recursive interpretation in `M`, so every body supplied to the iterator belongs to the admissible class. The same induction proves equivariance of all term operations.

If two primitive recursive descriptions give the same actual function on `M`, PA induction proves that their iterates agree at every counter. Thus projected iteration is independent of the description. If two bodies give the same actual function on `D`, the iterator uses the same argument `h`; this proves `Ext`. Parameters, capture-avoiding substitution, and nested iterator bodies are handled compositionally. The construction is a structure for the staged first-order signature, not merely a valuation missing substitution or congruence.

## Constant-target induction, including the quantified strengthening

Each standard numeral has a singleton fiber. Consequently an atomic equation `t=k`, or its reversal, holds in `D` exactly when its projection holds in `M`. The same applies to a fixed closed-term target: every closed term has a standard numeral value, by structural induction and ordinary finite iteration at its standard-valued counters.

This truth equivalence extends through falsity, conjunction, disjunction and implication in the two classical structures. It also extends through unrestricted universal and existential quantifiers because projection is surjective. Hence it holds for every first-order formula built exclusively from constant-target atoms. Actual equality between two unrestricted terms is not in this fragment merely because one term is a parameter.

For contextual induction, fix a valuation satisfying the retained context. Its premises provide the base and universal step. Transfer those to `M`, apply PA induction to the translated finite first-order formula, and reflect each conclusion. The eigenvariable condition ensures the context remains true as the induction variable varies. No projection of the context is required.

The quantified strengthening is a valid additional property of the countermodel. It should not be described as an induction fragment already derivable in iPRA: under an ordinary arithmetic interpretation, characteristic terms can turn arbitrary equations into zero tests, so quantified induction of this kind can have greater strength than iPRA. The main answer to the existing `T_cal` question uses only the theory's original numeral induction.

## Explicit failure of literal-equation induction

Take the parameter-free equation

`E(n): I(S(n),0;u.h(u)) = S(S(n))`, with `h(u)=S(C(u,1,u))`.

The base is derivable by computation: the left side at zero is `h(0)=2`, equal to the right side. Under `E(n)`, successor computation gives

`I(S(S(n)),0;u.h(u)) = h(I(S(n),0;u.h(u))) = h(S(S(n))) = S(S(S(n)))`.

These are computation and equality steps, so the induction step is derivable without induction. If `n=(b,1)` with `b` nonstandard, the prescribed exceptional orbit makes the left side `(b+2,0)`, whereas the right side is `(b+2,1)`. Thus the conclusion fails.

This explicit counterexample remains valid while every numbering law and fixed-point law holds. The old counterexample `I(n,0;u.S(u))=n` is invalid here because it is precisely `N_0` and is now true.

## Definable recovery and finite parameters

Every automorphism of an iPRA model preserves its parameter-free definable strict linear order. A finite-order order-preserving automorphism is the identity: a strict move would produce a strict cycle by iteration.

An interpretation induces an action on its definable domain and quotient. If the source is definably recoverable by a back-interpretation and return isomorphism, this action is injective: an automorphism acting trivially on the interpreted structure acts trivially on its back-interpretation, and naturality of the definable isomorphism forces it to be trivial on the source.

Fix all parameters of both interpretations and of the return isomorphism. For parameters in the interpreted quotient, include a finite tuple of representatives in `D`. An unused successor-chain flip still fixes this enlarged finite tuple and is nontrivial of order two. Its induced automorphism of the iPRA model is trivial by the order argument, contradicting injectivity of the action.

The parameter qualification is necessary: the comparison maps and parameter conditions must exist in this countermodel. This includes ordinary parameter-free bi-interpretations and finite-parameter theory interpretations with provably inhabited parameter conditions. The argument does not address an unrelated extension by a parameter condition deliberately unrealizable in the countermodel.

## Precise novelty and limits

The article already proves two different obstructions. Its numbering model validates `T_cal` and has a global involution fixing all standard numerals, but that involution moves every nonstandard point. Its `T_fus` model has involutions fixing arbitrary finite tuples and validates fusion, but it fails `N_0`. The incoming coverage models also have finite-parameter involutions, but do not supply all the numbering laws together with injective successor. None of these statements closes the named finite-parameter question for `T_cal`.

The new contribution is the three-element fibers with a fixed label, independent chain flips, and stabilizer-fixed path selection that preserve **all** `N_k` while leaving an involution after **any finite tuple** is named. Fixed-point preservation and the explicit exceptional-update counterexample are compatible additions. The abstract automorphism obstruction, the original finite-fiber idea, and the earlier parameter-free numbering obstruction are inherited.

No claim is made of an absolute complexity lower bound, a smaller positive presentation of iPRA, failure of equiconsistency, or absence of all one-way interpretations. Classical compactness and choice are used only in the metatheoretic countermodel construction. No new Lean/Rocq verification is supplied.
