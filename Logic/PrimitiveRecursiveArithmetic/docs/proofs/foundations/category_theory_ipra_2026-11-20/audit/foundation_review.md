# Independent audit of the proposed foundation

This note is a mathematical review of the design, not a claim of machine verification.

## 1. FinSet arrow codes and empty cases

The proposed code is sound: a map `n -> m` is a natural number `c < (m+1)^n` whose `n` radix-`m+1` digits are all `< m`. Define every digit, rank, selection and encoding function totally, with a specified arbitrary fallback on invalid inputs. Prove laws under the arrow-validity hypothesis.

- If `n=0`, the bound is `c<1`, so the unique map has code `0`, for every `m`, including `m=0`.
- If `m=0<n`, the digit condition is impossible, so there are no arrows to the empty finite set from a nonempty finite set.
- With primitive-recursive exponentiation defined by `a^0=1`, the number of valid raw codes is `m^n`, including `0^0=1`.
- For an exponential, rank and bounded selection of valid raw map codes provide the needed bijection with the object `m^n`. Evaluation is digit lookup after selection, and currying encodes each row before taking rank.
- When `m=0<n`, the exponential object is empty. A map `k*n -> 0` forces `k=0`, so currying still has the correct type. When `m=n=0`, the exponential has one element and evaluation has empty domain.
- Products use `n*m`; division by zero on invalid values is harmless if the total coding functions have defaults and laws are only asserted for coordinates below `n*m`.

The count identity, rank/select inverse laws, and table-composition laws are uniformly provable by quantifier-free induction because all finite-domain assertions can be replaced by their primitive-recursive characteristic functions. The report should say this explicitly rather than invoke induction on a bounded formula without explaining the characteristic-function conversion.

## 2. Coequalizer algorithm: invariants needed

Let `f,g : r -> n`. Start with labels `L_0(a)=a` for `a<n`. At stage `i<r`, put `p=L_i(f(i))`, `q=L_i(g(i))`, `u=min(p,q)`, `v=max(p,q)`, and replace every label equal to `v` by `u`. This gives a primitive-recursive iteration on the encoded label table.

Required invariants are:

1. `L_i(a)<n` for `a<n`, and `L_i(L_i(a))=L_i(a)`.
2. Every processed pair has equal labels: for `j<i`, `L_i(f(j))=L_i(g(j))`.
3. For each fixed *coded* finite-set map `h:n->k` with `h f=h g`, `h(L_i(a))=h(a)` for every `a<n`.

The third invariant is crucial. Idempotence alone would not prove the coequalizer property. For its induction step, the old invariant and the equality `h(f(i))=h(g(i))` imply `h(p)=h(q)`, hence `h(u)=h(v)`. Replacing a label `v` by `u` therefore preserves every `h` value. Quantifiers over `h` and `k` can remain external parameters of the induction; the induction formula itself is a primitive-recursive finite check over `a<n`.

At the last stage let `R={a<n : L_r(a)=a}` and `q=|R|`. Define `s:q->n` by bounded selection in `R`, and define the quotient map `e(a)=rank_R(L_r(a))`. Then `s(e(a))=L_r(a)` and `e(s(v))=v`. The second identity proves surjectivity without choice. For a cocone `h`, set `bar_h(v)=h(s(v))`. The third invariant proves `bar_h e=h`. If `t e=h`, evaluate at `s(v)` to get `t(v)=h(s(v))=bar_h(v)`, proving uniqueness.

Avoid a blanket claim that this algorithm produces the least equivalence relation among all arithmetic relations: uniform induction on such an arbitrary relation would need additional justification. Its universal property among coded finite-set arrows is enough and has the quantifier-free proof just described.

## 3. Total-machine-map presentation

A one-object category of total computable endomaps of the natural numbers fits the schematic presentation framework. Let `Run(e,x,y,t)` be a primitive-recursive relation checking a bounded trace, and define:

`Tot(e) := forall x, exists y,t, Run(e,x,y,t)`.

Arrow equality can be:

`Eq(e,d) := forall x,y,z,t,s, Run(e,x,y,t) and Run(d,x,z,s) -> y=z`,

restricted to valid (`Tot`) arrows. Determinism proves reflexivity. Totality of the intermediate arrow is needed for the transitivity proof: pick its output for the given input, then use the two equality premises. This is legitimate existential elimination and needs no choice function.

A primitive-recursive code constructor `comp(d,e)` is sufficient, provided the report specifies the following trace theorem:

`Run(comp(d,e),x,z,t) <-> exists y,u,v, Run(e,x,y,u) and Run(d,y,z,v)`

with appropriate existential quantification on the composite trace and with primitive-recursive forward trace construction and bounded reverse trace extraction. More precisely, the clean semantic statement is equivalence of `exists t` on the left and `exists y,u,v` on the right. A particular composite trace need not correspond to every pair of component traces.

This trace theorem, deterministic identity traces, and finite trace-compilation correctness yield closure under composition and the category laws. The bounded trace checker is uniformly primitive recursive; no total universal evaluation function is asserted. The optional example represents computable maps, not all mathematical functions. A one-object category of all endomaps of N is not cartesian (there is no terminal object), and no cartesian-closedness claim should be attached to it.

## 4. Schematic transport and induction boundary

Finite equational/intuitionistic category proofs with arbitrary arithmetic `Obj`, `Hom` and `Eq` formulas transport to iPRA by formula substitution. The correct statement is a metatheoretic proof transformation or a Lean function transforming derivation objects. It is not internal uniform truth or reflection for arbitrary arithmetic formulas.

**Substantial boundary:** from a chosen terminal object and chosen binary products, one obtains products of each *fixed* finite list by a finite proof schema. A theorem uniform in the list length needs a separate argument: induction on `Obj(product(list))` or on an unrestricted universal-property formula is not automatically quantifier-free. Thus state the general finite-limit construction for each fixed finite diagram, or assume a uniform finite-product operation with its laws. Uniform arbitrary-length results are justified for the decidable FinSet presentation via the finite-check encoding described above.

## 5. Density and equivalent labels

The completed `sections/yoneda.tex` handles this correctly. If `x ~ x'` in `P(a)`, then `id_a` is an arrow `(a,x)->(a,x')` of the category of elements because `P(id_a)(x') ~ x' ~ x`. The cocone condition on this arrow proves equivalent labels give equal mediator values. No extra quotient on object codes is needed.

Category-of-elements arrow equality is the base category's typed hom equality. Its validity is stable under that equality by congruence of the presheaf action. Composition validity follows from action composition and fibre congruence. The density quotient's least-congruence formulation explicitly includes both fibre and hom equalities; the proof then normalizes a generator through the arrow `f:(b,P(f)x)->(a,x)` in a fixed number of steps. All these calculations are finite, so arbitrary arithmetic equality causes no induction problem here.
