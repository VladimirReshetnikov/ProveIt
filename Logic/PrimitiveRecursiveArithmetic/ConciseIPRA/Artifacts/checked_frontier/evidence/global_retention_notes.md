# Delayed target opening with global fresh names

## Status and scope

This is a written metatheoretic argument for the integer/list certificate contract, relative to the inherited sorted arity decoder and its soundness/completeness theorem. It is not a proof-assistant verification of Python. It establishes that delaying a retained target opening until after a recursively checked minor proof is **not automatically unsound**. The new variables admitted during that proof can be discharged by a known simultaneous instance.

The retained-export lemma addresses the opening order used in `work/root/retained_three_tokens.py` as inspected in this session. **The result being claimed is the scoped-export lemma, not a completed equivalence proof for that entire raw checker. Sections 6 and 7 are preliminary integration notes.** The global floor is an integer, initially zero; each non-hypothesis continuation decrements it once. A recursive premise receives a tuple copy of the retained context. It cannot mutate the caller's tuple or its entries. No statement below covers arbitrary Python objects, fractional coordinates, JSON booleans as a separate mathematical syntax, resource-threshold equivalence, or nonterminating input processing.

The existing local retained-major report explicitly leaves delayed global opening unaudited. The result here supplies a separate argument; it does not claim that the old same-floor proof applies unchanged.

## 1. Sorted raw decoder

Use the exact decoder of the inherited arity report. A numerical protected slot has width two. At numerical depth `3+2p`, coordinates 0,1,2 denote zero; coordinates `3+2j` and `4+2j` denote protected slot j for `0 <= j < p`. At formula depth `2p` there are p protected numerical slots. Negative integers at least the current floor K denote rigid numerical parameters.

The numerical readings of arrays are:

| Arity | Reading | Relevant child environments |
| --- | --- | --- |
| 0 | 0 | none |
| 1, `[b]` | successor of b | prepend two zero slots |
| 2 | 0 | ignore both annotations |
| 3, `[n,a,h]` | `I(n,a;v.h)` | prepend zero for n,a; prepend v for h |
| at least 4 | 0 | ignore all children |

The formula readings are:

| Arity | Reading | Relevant child environments |
| --- | --- | --- |
| 0 or scalar | truth `0=0` | none |
| 1, `[B]` | `D_{x,y} B` | prepend y,x |
| 2, `[s,t]` | numerical equality | decode both children numerically |
| 3, `[P,U,B]` | `Q_y B` | only the THIRD child is meaningful; prepend y |
| at least 4 | truth `0=0` | ignore all children |

For a template at floor K, any meaningful numerical leaf outside its protected interval and outside the live negative names is the distinguished numerical hole. Formula scalar padding is always truth and does not carry a numerical hole. Meaningful constructors have the depth increments `5-arity = 4,3,2`, exactly as in the executable opener. Ignored children may still be traversed operationally and may cause rejection. A successful traversal cannot give them mathematical content.

Write `O_K(T,u)` for a successful executable opening of a raw formula tree T at formula depth zero with image u. Write `D_K(T;v)` for its sorted decoded one-hole native formula, before filling the hole. Semantic Opening says that the decoded result is `D_K(T;U)`, where U is the decoded numerical image. If the image is semantically unused, choose U=0; the executable need not have inspected that image.

All equalities between decoded formulas below are syntactic identities up to the ordinary bookkeeping of protected binders, or provable identities of their stipulated constant annotations. They are **not claims that the raw arrays are equal** or that opening is raw-idempotent.

## 2. A generalized fresh-instance supply rule

Let Γ and A contain none of the distinct numerical parameters j1,...,jr. Let each v_i be a numerical term containing none of these parameters. If

    Γ proves H(v1,...,vr)
    Γ,H(j1,...,jr) proves A,

then Γ proves A. Substitute v_i for j_i throughout the second derivation. The old context and its conclusion are unchanged; cut in the first derivation. This uses admissible capture-free substitution and cut in the full native calculus (or directly in iPRA). It neither assumes consistency nor asserts that H holds for arbitrary values of the new names.

Equivalently, the first premise proves the existential closure of H, and the second premise eliminates that closure. The substitution proof is sufficient and makes the exact chosen instances explicit. The inherited known-zero-instance supply is its special case `v_i=0`.

## 3. Moving-floor opening lemma

Let L <= K be integer floors, and put

    J = {L,L+1,...,K-1}.

Let u be a numerical raw expression already checked in the old scope K. Let U be its decoded term, which therefore contains no meaningful member of J. Let F(v)=D_K(T;v). Suppose the later opening `O_L(T,u)` succeeds, and call its decoded result H. If σ simultaneously replaces every parameter in J by U, then

    H σ = F(U).

There is no requirement that `O_K(T,u)` itself have an operationally successful execution: the right side is the mathematical filling of the old decoded template. This distinction matters for ignored annotations.

### Proof

Proceed by structural induction on the sorted relevant raw tree, carrying its protected-slot environment.

At a meaningful numerical scalar there are four cases. An old live rigid name is unchanged by both floors and by σ. A protected nonnegative coordinate denotes the same slot at both floors. A new live name j in J was an old hole; the later opening retains it and σ replaces it by U. Every other numerical hole is filled by u during the later opening, whose root validation yields U and whose old-scope free parameters are fixed by σ. Thus all four cases agree with filling the old hole by U.

At successor, iterator, equality, D and Q, recurse on precisely the meaningful children, with the environments in the tables. U has no protected free coordinate at its numerical root and contains no new name, so its insertion and σ commute with these binders. In the iterator's update the local state is preserved; in its counter and initializer the extra slot is zero.

Numerical binary nodes and numerical nodes of arity at least four decode as zero. Formula scalars, empty arrays and formula nodes of arity at least four decode as truth. The first two fields of a ternary formula are ignored. All these cases are immediate even if the executable traversal changed their raw annotations while moving floors. The proof is about successful decoded outputs, not an additional sorted meaning for negative depths inside ignored annotations.

This proves the lemma on arbitrary finite integer/list aliases admitted by the inherited decoder, not only canonical object expressions.

## 4. Retained equality: delayed target opening is sound

Suppose the forward dispatcher selects a retained equality `[s,u]`, with s truthy. Let K be the floor before checking the minor, and L the floor after that check returns. Its tuple context Γ is unchanged. Because the retained equality was previously checked, its meaningful source and target terms S,U use only old parameters; occurrences in ignored annotations do not count as free variables.

The source opening is computed at K, before recursion. With F(v)=D_K(T;v), the recursive proof establishes `Γ proves F(S)`. The retained major establishes `S=U`, so equality transport in the native calculus establishes `Γ proves F(U)`.

The delayed target is H, decoded from `O_L(T,u)`. By the moving-floor lemma, replacing every member of J by U gives `Hσ=F(U)`. Every member of J is absent from Γ and the caller's goal A: a meaningful occurrence would have failed their old no-image scope checks. Hence the fresh-instance supply rule makes it sound to retain H for the continuation and then discharge its new parameters.

The common continuation decrements the floor once more and reopens H with either zero or that final fresh parameter. H has already been successfully opened, so it has no meaningful unresolved hole. Its decoded reading is unchanged by this last successful opening. The last fresh parameter is also absent from Γ,A,H and can be eliminated arbitrarily.

The correct conclusion is a supplied fresh instance. H itself need not be a consequence of Γ uniformly in the values of J. For example, with S=U=1 and a negative coordinate that was an old hole, the source can be `1=1` and the delayed target `j=1`. The latter is not valid for every j; its instance at j=1 is exactly what justifies exporting it in a continuation whose final goal does not mention j.

## 5. Retained closure: delayed target opening is sound

Suppose s is false, so the expected retained major is `[T,T,T]`. Its reading is `Q_y B(y)`, namely `B(0) -> forall y B(y)`. The false integer/list source aliases decode numerically as zero. Since the major is retained, its meaningful matrix has no free name newly admitted while checking the minor; its y slot was protected under Q.

The source opening at K decodes as B(0). The recursive minor proof and the retained closure establish `forall y B(y)` in Γ. The later target opening at L decodes as B(U_L), where U_L is a numerical term in the enlarged scope. If the image is semantically unused, take U_L=0.

Substitute zero for every new name in J. Then `Hσ = B(U_L σ)`, an ordinary old-scope instance of the established universal closure. Consequently Γ proves Hσ. Apply the fresh-instance supply rule to the continuation. The final common opening again preserves the decoded closed result.

Unlike the equality case, there is no need to give all new names the target value. Universal specialization permits every target term; zero substitution is a convenient way to remove its new free parameters.

## 6. Preliminary whole-program soundness plan (not an asserted theorem)

Use induction on the finite tree of recursive checks and continuation steps. The maintained invariant is that the decoded entry context and entry goal have no meaningful rigid parameter below their entry floor. Tuples prevent a premise proof from adding its local assumptions to its caller's context.

Hypothesis closure is inherited. The retained equality and closure branches are Sections 4 and 5 above. A nonzero paired major s is checked before opening; after its recursive proof, its meaningful variables are still in the older scope, so its tripling and the next fresh witness use the inherited D-elimination argument. Non-unary majors contribute only the inherited truth aliases. Introduction has its witness checked before its next fresh variable and uses progress only at literal binary equality; other meaningful matrix roots use cases.

The computation branch uses the same constructed iteration equations as the incumbent. Replacing the old independent major flag by source s can choose a fresh image in an additional successor-computation case, but the inherited known-zero-instance supply theorem already justifies either image for this branch. The caller's goal and context omit that new name. No uniform theoremhood of the supplied fresh equation is assumed.

If the remaining inherited-branch interfaces and the precise implementation invariants are discharged, this plan would show that each successful finite integer/list execution on a canonical public goal yields a native derivation. The scoped-export lemma itself supplies only the newly needed retained-branch argument. **This note does not assert completed whole-program soundness, completeness, or bi-interpretability for the candidate file.**

## 7. Preliminary canonical completeness and three-field compression

Use compiler-normal canonical proofs of the local retained calculus, as in the existing retained-major package. Every numerical term has only unary and ternary array constructors and scalar leaves. Every meaningful formula has a binary equality node somewhere; canonical Q has three identical formula-body fields. Every computation supply and every retained forward result is closed at the current live scope before its last reopening. Contexts also may contain scalar or high-arity administrative truth entries.

### Global allocation

Translate derivations, not fixed certificate bytes. Carry an injective map from the source's currently live rigid parameters to the globally allocated target names. When a recursive premise consumes names, keep the map on old parameters and choose the next target eigenparameter only when its source introduction or elimination is compiled. Parameters local to the finished premise have no meaningful occurrence in the source target template. Therefore the delayed opening of every compiler-normal retained target has the same decoded result as opening it before recursion. Protected positive slots are unchanged; only rigid negative names are renamed.

Strengthen the compiler induction to allow additional canonical context entries and an arbitrary such injection, exactly as in the local retained append lemma. Closed supplies remain independent of the ultimate goal's arity. The extra allocated names may be unused; their presence in the global numerical scope causes no completeness loss. This is the proposed canonical global-allocation transfer for the four-field retained presentation; a complete compiler proof still needs these invariants formalized together.

### Three packet fields

The three-field packets are `[s,u,t]`.

* For a retained forward step, its major is already determined by these fields and no separate m is needed.
* For computation, retain s,u,t from the old packet; u is a certified syntactically nonzero seed.
* For paired introduction, use s=u=0 and let t be its numerical witness.
* For paired elimination, put its unary D major in s, set u=0, and choose an inert t such as zero.

On the compiler-normal closed supplies, changing the final image selector from the old m flag to s has no effect: there is no meaningful hole to fill. For D opening and introduction the flag has precisely its intended old value.

### Priority collisions

Introduction cannot collide with the retained branch: its expected closure is `[t,t,t]`, with t a numerical term. Such a term has no binary node, whereas a canonical formula body has one. Thus it cannot be a canonical retained closure; other retained root arities differ.

Paired elimination also cannot collide in these contexts. Its expected equality is `[s,0]`, where s is a canonical unary D formula. The tree s contains a binary equality node somewhere. A numerical term occurring as a side of a canonical retained equality has only unary/ternary constructors, so it cannot equal s. Other context roots have arity one, three, zero, or at least six. This is an exact syntactic separation, not an appeal to consistency or explosion. It concerns the canonical compilation invariant; arbitrary raw traces may have such a collision and are handled by the soundness proof.

Zero computation cannot collide for the same numerical/formula separation: its expected closure has the numerical update t as body.

For successor computation, the possible collision `[s,u]` is repaired by the inherited fresh seed alias. Choose a marker numeral r absent from the finite current context, put `U=I(0,u;v.r)`, supply U=u by zero computation, supply the desired successor equation with seed U, then forward-transport its complete seed template from U to u. The first supply cannot collide; the second expected equality `[s,U]` is absent by the fresh marker and differs from `[U,u]` because u is a proper smaller subtree of U. The final forward step has its equality major retained by construction. All parameters in these supplies are already live, so the closed-supply invariant survives.

The append lemma for compiler-normal equations and closures therefore still applies. Native transport or closure elimination first appends its major proof, then uses a retained forward instruction, and closes from the resulting hypothesis. Simultaneous induction on native derivations supplies both the ordinary compilation and its appendable equational/closure form. The global renaming invariant and the collision arguments above are a plausible route to proving that three-field compression loses no canonical public theorem. That entire compiler theorem is **preliminary**, not part of the scoped-export theorem established here.

## 8. Verification boundary

The new opening argument has been independently checked in this session by another mathematical agent. It remains a written proof, dependent on the inherited arity decoder and native-calculus bridge. No claim is made that a finite test suite proves the theorem. A production compiler would still be useful evidence for the constructive completeness argument, particularly its fresh-marker collision repair and allocation map.

The currently inspected global file measures 250 significant tokens, 279 AST nodes and 566 normalized bytes according to the parent's measurement. Those numbers do not by themselves beat the repository's complete coordinate envelope. The present result should not be presented as having achieved that optimization target.
