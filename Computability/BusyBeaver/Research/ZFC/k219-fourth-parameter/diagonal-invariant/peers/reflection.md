# Independent audit of the modified-rho8 syntactic invariant

This is a source-level ordinary mathematical review of `drop_contract`'s proposed invariant for the **specific** replacement `rho8(a,b,c,wel a b)`. It is not a Lean check and does not assert the same proof for other operand choices such as `wel b c`. No bounded proof search was needed for this audit.

Write `I`, `R`, `Q`, and `E` for the literal numerical constructors in `Code254`, with `F=1=R(0,0)` and `0=I(0,0)`. Constructors have residues 0,1,2,3 modulo four. Every constructor is injective in its two arguments, including `I`; only the separate truth notation has the special zero alias. In particular `R(a,b)>a,b`, and `I(x,y)>x,y` if at least one input is nonzero. These facts follow from the Cantor pair inequalities already stated in `Code254`.

Let S be the least class containing truth, every literal retained axiom and gated bundle, every restricted rho8 instance, and every identity `I(x,x)`, and closed under

- generalization: `S(p)` implies `S(Q(i,p))`;
- quantifier monotonicity: `S(I(p,q))` implies `S(I(Q(i,p),Q(i,q)))`.

Modus ponens is deliberately **not** a constructor of S. All S generators have root residue 0 or 2, so no membership- or equality-headed code belongs to S. Moreover `S(Q(i,p))` implies `S(p)`: the only generator with root residue 2 is generalization, and constructor injectivity recovers its premise.

The following inversion claims suffice for MP closure. Each is proved by cases on the final S constructor, with no assumed propositional completeness or substitution principle.

1. **No negated equality:** `I(E(a,b),F)` is not in S. An identity would require `E(a,b)=F`; monotonicity has a Q-headed antecedent; rho3/rho5/G have an implication consequent rather than F; the remaining axiom antecedents have root Q or I, not E. Truth and generalization have incompatible shapes.
2. **No rho6 antecedent:** `Ex_i Q_i p = I(Q(i,I(Q(i,p),F)),F)` is not in S. Its antecedent is Q-headed and its consequent is F. The only initial row with this root pattern is rho1, whose equality body would have to equal `Q(i,p)`. The tag mismatch excludes this. An identity would require Q-headed code equal F; monotonicity has Q-headed consequent. The other initial rows have an incompatible antecedent or consequent.
3. **No bundle antecedent:** `I(V,nks)` is not in S, where `V=I(R(a,b),Q(c,R(a,b)))` and `nks` is Q-headed. Its antecedent is I-headed and consequent Q-headed. The only initially plausible row is rho6, whose inner antecedent begins with Q, whereas V begins with R. Identities would require V=nks. Monotonicity begins with Q. All other constructors fail an outer tag comparison.
4. **Restricted-rho8 trigger:** if `S(I(I(c,R(a,b)),a))`, then `a=b=0` (and the final S generator is a rho6 instance). The rho6 comparison forces `R(a,b)=F`, hence a=b=0. All other ordinary rows fail antecedent tags or the bundle's Q-headed nks. An identity would require `a=I(c,R(a,b))>a`. A restricted-rho8 generator with parameters `a',b',c'` would force `a'=R(a,b)>a` while its consequent gives `a=I(I(a',c'),I(b',c'))>a'`. Both are impossible. Truth's zero alias cannot match because R(a,b) is positive; generalization and monotonicity have incompatible root/antecedent tags.

For the final claim, comparing two restricted-rho8 shapes also gives `c=I(c',R(a',b'))`, but that equality is unnecessary: the displayed strict cycle already excludes the case. This is precisely where using **A as an operand of the computed atom** matters; it must not be silently generalized to another builder.

Now prove MP closure `S(I(p,q)) -> S(p) -> S(q)` by induction on the construction of the major premise:

- Truth has p=q=0; identity has p=q. Their minors already give the conclusion.
- rho1 would require `S(Q(i,I(E(i,j),F)))`; stripping Q contradicts claim 1.
- rho2 strips Q from its minor and applies the monotonicity constructor.
- rho3, rho5 and G require an equality-headed minor, excluded by the root invariant.
- rho4 strips two Qs from its minor and reapplies generalization in the opposite order.
- rho6 and bundle are blocked by claims 2 and 3.
- Restricted rho8 uses claim 4. Since a=b=0, its conclusion is the admitted identity `I(I(0,c),I(0,c))`.
- A generalization constructor cannot itself be I-headed.
- For a monotonicity constructor, strip Q from the minor, use the induction hypothesis on the underlying implication premise, then generalize the resulting consequent.

Therefore every derivation in the modified literal calculus lies in S by induction on that derivation. Since F is membership-headed, F is not derivable. The proof is entirely finitary and uses elementary constructor arithmetic; it can be expressed in ZFC (and plausibly much weaker arithmetic, which is not claimed here). Consequently ZFC proves consistency of this modified calculus. Under consistency of ZFC and the usual arithmetization, it cannot also be ZFC-provably equiconsistent with ZFC without contradicting the second incompleteness theorem.

This audit preserves the complete gated K bundle unchanged. It neither projects its apparent conjuncts nor treats negation classically. It also uses no semantic model-existence assumption. The ordinary proof depends on a formalization faithfully including **all** literal initial rows and the two added S closure rules. A Lean proof, if requested, should first establish constructor injectivity/tags and the four inversion lemmas; no finite-algebra search result is a premise.
