# Template-free crossed rewriting: verified equivalence proof

## Verdict

The new primitive G is sufficient for all ordinary equational transport. The clean proof uses oversized computation aliases, not induction, numerical cases, a normalization theorem, fresh-variable discharge, or substitution into new derivations. Only G and the zero-iterator computation axiom I0 are needed for equality recovery.

The complete proposed kernel may use Hyp, I0, IS, G, ordinary QE, ordinary DE, and the existing witness-sensitive DI. It has the same full native Eq/Q/D language as NPrf. The existing ordinary iPRA interpretations and both composites transfer after the exact-sequent equivalence below.

## The precise primitive

Given two proved equations in the same retained context:

    Gamma |- s=t        Gamma |- u=v
    -------------------------------- G
              Gamma |- v=R_(s->t)(u)

There is no supplied numerical or formula template. R is a fixed syntax operation: replace every capture-safe exact occurrence of source s in u by t. Test for a match at the current root BEFORE descending; when a match is found, return the target immediately and DO NOT scan the newly inserted target. Under binders, use the corresponding lifted/renamed source and target, or a locally nameless representation in which well-scoped open parameters are rigid free names. R must never confuse a locally bound variable with a free source variable. Alpha-equivalent presentations are identified, or a canonical binder representation is used.

In particular R_(s->t)(s)=t, for every s,t, including s=t, source literal0, sources containing iterators, and targets that themselves contain the source. The latter case is safe because this is one pass, not repeated normalization.

## Elementary equality algebra

Write J(a)=I(0,a;z.0). Its equation J(a)=a is I0.

1. Common-left join is an immediate G instance:

       s=t, s=u  =>  u=t.

   The minor's left endpoint is exactly the major's source, so the root match returns t. No proper-subterm behavior matters here.

2. Reflexivity: use J(a)=a as both premises of common-left join. The conclusion is a=a.

3. Symmetry: from a=b and reflexivity a=a, common-left join with major a=a and minor a=b gives b=a. Equivalently, a proved0=0 as major makes R_(0->0) the identity and reverses any minor equation. The first proof needs only the root-match identity.

4. Transitivity: from a=b and b=c, symmetry gives b=a; common-left join with major b=c and minor b=a gives a=c.

All four constructions work in an arbitrary retained context. No structural numerical substitution is used.

## Oversized-marker lemma

Let H(x) be any fixed numerical term template, with the displayed hole variable x fresh from all passive parameters s,t. Repeated and zero occurrences of x are allowed. Let |T| count term-constructor and variable nodes, including iterator bodies. Alpha-renaming and lifting of open variables preserve this count.

Choose N=1+|H|+|s|+|t| and set

    K := I(0,s;z.S^N(0)).

The update S^N(0) is closed and ignores z. K itself need NOT be closed: it has precisely the passive free parameters of s. I0 immediately proves K=s. Also |K|>|H|, |K|>|s| and |K|>|t|. A larger N is equally acceptable.

Every capture-safe occurrence of K in H(K) is one of the copies planted at the distinguished occurrences of x:

- An occurrence disjoint from every planted K lies entirely in a passive part of H, whose size is less than |K|.
- An occurrence properly inside a planted K is too small to equal K.
- An occurrence properly containing a planted K is too large to equal K.
- Tree occurrences are either disjoint or nested, so these exhaust possible unintended occurrences.

The argument applies under iterator binders: capture-avoiding substitution plants the corresponding lifted/renamed copy of K, and those operations preserve size. Consequently

    R_(K->s)(H(K)) = H(s),
    R_(K->t)(H(K)) = H(t)

as finite syntax, up to the agreed alpha-equivalence convention. These are syntactic identities in the metaproof, not equality-transport steps of the proposed calculus. They remain true if H has no distinguished occurrence.

## All numerical congruence

Suppose Gamma |- s=t. I0 supplies Gamma |- K=s; transitivity supplies K=t. Reflexivity supplies H(K)=H(K).

Apply G with major K=s and this reflexive minor. The marker lemma identifies its conclusion as H(K)=H(s).

Apply G with major K=t and the same reflexive minor. Its conclusion is H(K)=H(t).

Common-left join with the latter as major and the former as minor yields H(s)=H(t).

This is a proof construction for every finite H; H is used only by the untrusted compiler/metaproof to construct K and the displayed terms. H is NOT an additional argument of G or a hidden checker input. The checker sees ordinary computation equations and ordinary G applications. The certificate can be larger; a checker-size improvement must still be measured.

## Full two-sided equational transport

Given s=t and a(s)=b(s), the preceding congruence gives a(s)=a(t) and b(s)=b(t). Symmetry and transitivity compose

    a(t)=a(s)=b(s)=b(t).

Therefore the exact old equational Tr primitive is admissible. All contextual parameters are retained throughout; no term assignment is substituted into an existing proof.

## Soundness of G in NPrf

For fixed s,t,u,v, mark the source occurrences that the one-pass operation replaces in u. They are disjoint because the algorithm stops at a match. Replace those marked occurrences by a fresh numerical hole x, obtaining a numerical template H(x), with binders freshened as usual. Then u=H(s) and R_(s->t)(u)=H(t) as syntax. Native equational transport applied to major s=t and minor H(s)=v yields H(t)=v. Native symmetry yields v=H(t), exactly G's conclusion.

This direction only uses the already available old transport. It does not assume congruence or substitution in the new kernel. If no occurrence is replaced, H is constant; this is allowed by the old rule.

## Structural lemmas before equivalence

Weakening, injective renaming/alpha-renaming, and cut on a retained formula are admissible by proof induction. Renaming preserves exact syntactic matching and commutes with the capture-safe replacement operation. Cut changes the provenance of Hyp leaves, not their terms; it does not alter source matching or the witness-sensitive DI test. At eigenvariable rules, rename the eigenvariable away from the inserted proof first.

Do NOT initially assert arbitrary numerical substitution by direct induction: substitution can create additional exact matches of s in u, and can turn a witness into literal0. Arbitrary substitution becomes admissible after exact equivalence with NPrf is proved. The equality argument above does not need it.

## Recovering the current introduction rules

Let new DI use progress exactly when its matrix is a literal equation and its witness is literally0, and cases otherwise.

Atomic Q-progress is derived by introducing D_(r,y)E(y), with r unused, witness0, and the supplied progressive premise E(z) |- E(Sz). DE exports Q_y E(y).

Ordinary DI-case is already primitive unless its matrix is an equation E and its witness is literally0. For that exception put w=I(0,0;z.0). It is syntactically nonzero and I0 proves w=0. Under the local E(w,0), recovered equational transport gives E(0,0); cut in the supplied old case premise to get E(0,Sz); transport along derived0=w to get E(w,Sz). New DI with witnessw is in case mode and concludes the original D_(x,y)E(x,y).

This bootstrap is acyclic: ordinary equational transport was recovered first from G and I0 alone. The exceptional DI construction needs only ordinary-assumption cut, not numerical substitution into derivations.

## Exact-sequent equivalence and iPRA

New -> NPrf: translate proof trees inductively. G uses the soundness argument above; case-mode DI is old DI-case; progress-mode DI is the old derived witnessed-progress rule (QI-progress then QE under the base then DI-case). Hyp/I0/IS/QE/DE are unchanged.

NPrf -> new: translate proof trees inductively. Equational Tr uses the marker/congruence construction; QI-progress and DI-case use the preceding derived introductions. All other rules are unchanged.

Thus Gamma |-new A iff Gamma |-NPrf A for ALL finite native Gamma and formulas A, without guarded public-language restrictions. Terms, Q/D ordinary readings, and designated contradiction0=S0 are identical. Apply this exact equivalence to every sequent in the inherited native/iPRA interpretation and round-trip proofs. This gives whole-domain, actual-equality bi-interpretability, the same identity numerical composites, both formula composites, and equiconsistency.

This is a written universal proof unless a separate formalization is actually compiled. Certificate tests cannot replace it. The claim of novelty should be limited to the inspected current proposal and incoming packages: one_context still has a supplied H, kernel_refinement still has a supplied one-hole C, and reversal_core still has a supplied arbitrary F. General equality by rewriting is classical mathematics; no literature-wide novelty claim is warranted.

## Optional alternative proof by fresh numerical alias

The earlier DE-based proof is also valid. Construct D_(b,y)(C(y,a,b)=a), where C(v,a,b)=I(v,a;u.b), using case DI at the nonzero syntactic witness J(a). The successor target follows from C(Sz,a,J(a))=J(a)=a, by IS and root transitivity; the local base is unused. DE exports Q_y(C(y,a,b)=a) with fresh b. I0 supplies the base; QE at1 gives C(1,a,b)=a; IS gives C(1,a,b)=b; common-left join gives b=a. This proves fresh-alias discharge by ordinary cut and DE. Under the alias b=s, transitivity gives b=t, and rewriting a reflexive H(b) at the fresh free variable b produces the two H(s),H(t) endpoints. Join and discharge finish congruence. The marker proof is preferable because it removes the logical dependencies.

## One-pass normalization is not the primitive

Do not replace R by an iterated normalizer in the specification or implementation. Arbitrary orientations such as0->S0 may grow forever if repeated. G uses exactly one root-first pass. The marker proof works for that operation directly and requires no choice of term order.
