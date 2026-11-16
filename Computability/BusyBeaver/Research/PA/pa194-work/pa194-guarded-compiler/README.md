# A guarded compiler from arithmetic derivations to the relational source theory

The direction `¬Halt(M₁₉₄) → Con(PA)` needs, in every candidate-PRA model whose arithmetic
reduct satisfies `𝗜𝚺₁`, a refutation in the relational source theory from a refutation in
`ordinaryPAeq` (`OrdinaryCompiler` of
[`pa194-model-logic`](../pa194-model-logic/ORDINARY-SOURCE-COMPILER.md)). The route there is
`conditional_compile`: an induction over an internal derivation that keeps a source
derivation of the translated sequent, with four rule suppliers left as hypotheses
(`RemainingRules`).

This directory replaces the invariant of that induction, proves the rules that are syntactic
for the new invariant, and reduces the compiler to an interface with no packet and no size
condition (`Interpretation`).

## Why the invariant has to change

`conditional_refutation` instantiates the packet as `rootParameters d`, whose free environment
is `d+1` copies of the source free variable `&0`, and the invariant is "the source theory
derives the translated sequent".

- A free variable of the arithmetic language is translated to a source variable, and the
  translation of an atom contains the domain formula of every variable it reads
  (`variableValue z x = Dom(z) ∧ z = x`). `ordinaryPAeq` derives the sequent `{&0 = &0}`, but
  the source theory does not derive its translation: in a model of the source theory with an
  element outside the ordinal domain, the translation is false at that element. So the
  invariant fails for a derivable sequent, and `RemainingRules U T (rootParameters d)` is
  false in the standard model for a large enough `d` (walk a derivation of `{&0 = &0}`: the
  rules already proved preserve the invariant, so one of the four fields fails).
- All free variables are sent to the same source variable. The premise of a universal
  introduction is derivable for a fresh variable; after the collapse the fresh variable is
  identified with the variables of the context, and the translated premise no longer
  entails the translated conclusion.

This is an argument on paper. No theorem here states that `RemainingRules` is refutable; that
would need a model of the source theory in Lean.

## The guarded calculus

`GDerivable T Δ`: the source theory derives `Δ` together with the guards `¬Dom(&i)` below
some bound. Because the bound is existential, guarded derivations combine by weakening. The
quantifier rules are relativized to the domain: a universal introduction turns the guard of
its eigenvariable into the domain hypothesis of the quantifier (`all_rel`), and an
existential introduction with a free variable as witness takes the domain formula of the
witness from the guards (`ex_rel`). At the root of a refutation the sequent is `{⊥}` and the
guards are removed one at a time (`discharge_guards`): the guard of `&0` is generalized, cut
against `∃x Dom(x)`, and the other guards move down by one index.

The packet is an *identity packet*: its free environment sends the free variable `i` to the
source free variable `i`, so distinct variables stay distinct. The translation under such a
packet does not depend on its length (`formula_ext`), which gives the translation `tr` of a
formula of arity zero and `trBody` of a formula under one binder, with no size condition.

## Modules

| Module | Content |
| --- | --- |
| `PA194GuardedCompile` | `guard`, `guards` with their definability, shift and membership lemmas, and `discharge_guards`: from `Provable T (∃x Dom(x))` and a derivation of `guards n ∪ {⊥}`, a proof of `⊥`. |
| `PA194TranslateShift` | `formula_shift`: for packets related by `EnvShiftRel` (every environment term shifted, the free environment re-indexed by one), the translation of `shift p` is the shift of the translation of `p`. Proved for every internally valid formula code by `𝚷₁` structural induction over terms (`term_shift`) and formulas, from shift lemmas for the fixed templates and the value constructors. `IdentityPacket`, `translateFormula_shift`. |
| `PA194TranslateSubst` | `formula_subst`: for a substitution of the arithmetic language whose entries are variables and packets related by `EnvSubstRel`, the translation of the substituted formula is a source substitution applied to the translation. `translateFormula_substs1_fvar`: instantiating the bound variable of a formula of arity one by a free variable. `translateFormula_free`: the translation of `free p` is `free` of the translation of `p` under one binder. |
| `PA194TranslateExt` | `formula_ext`: two packets that agree on the bound environment and on the free entries below both lengths translate a formula below both lengths to the same code. `idParam` (identity packets from Foundation's `fvarVec`), `tr`, `trBody`, and the lemmas `tr_and`, `tr_or`, `tr_all`, `tr_exs`, `tr_neg`, `tr_shift`, `tr_substs1_fvar`, `tr_free`. |
| `PA194GuardedCalculus` | `GDerivable` with weakening, the logical axiom, verum, conjunction, disjunction, cut, shift, `all_rel`, `ex_rel`, and `root` (a guarded refutation is a refutation when the domain is inhabited). |
| `PA194TrCompile` | `Interpretation U T`: for every internal axiom `φ` of `U` a guarded proof of `tr φ`; for every formula `p` of arity one and term `t` that is not a free variable, a guarded derivation of `{¬tr(p[t]), tr(∃p)}`; and `Provable T (∃x Dom(x))`. `tr_compile`: the induction over an internal derivation, all ten rules. `refutation_of_interpretation`: a refutation in `U` gives `Provable T ⊥`. |
| `PA194Leibniz` | `TermFacts T`: three facts about terms (below). `leibniz`: for every internal formula `p` of arity one, term `t` and free variable `c`, a guarded derivation of `{¬tr(&c = t), ¬tr(p[t]), tr(p[&c])}`. Opening a quantifier of `p` shifts the free variables of `t`, so the induction is over the coded triples `(p, t, c)` with the formula complexity as measure (`measured_bounded_sigma1_order_induction`); the quantifier cases use `free_subst_qVec` (opening the quantified variable of `q[#0, t]` gives `(free1 q)[shift t]`). `witness_of_termFacts`: the `witness` field of `Interpretation`, by eliminating `c` against `tr(∃x. x = t)`. `interpretation_of_termFacts` assembles `Interpretation` from `TermFacts`, the axioms and the inhabitation of the domain. |
| `PA194TermNames` | Three formulas of the arithmetic language in which the naming variable is quantified: `nameAll s s'` (every `x` with `x = s` has `x = s'`), `uniq s` (two names of `s` are equal), `exName s` (some `x` has `x = s`). `NameFacts T`: seventeen guarded facts, each about one function layer with arbitrary internal terms as arguments (below). `uniq_all`, `exName_all`: by induction over the term. `nameSubst`: names transfer along a substitution `a[u] ↦ a[w]` once they transfer from `u` to `w`, by induction over `a`. `termFacts_of_nameFacts`: `TermFacts T`. Because the naming variable is bound inside the formulas, no step of these inductions opens a quantifier: each is a cut. |
| `PA194ValueBody` | `valBody s`: the source formula of arity one saying that its bound variable is a value of the term `s` of arity zero. `translate_lift`: under a packet whose free environment is the identity, the translation of such a term is its value formula at the result term of the packet. `tr_peq`: `tr(s = s')` is `∃v∃w (valBody s at v ∧ valBody s' at w ∧ orderIso(v, w))`. `valBody_fvar`, `valBody_zero`, `valBody_succ`, `valBody_add`, `valBody_mul`, `valBody_shift`. These identities between codes prepare the proofs of `NameFacts`, in which the value formulas of the arguments are parameters; no field of `NameFacts` is proved. |
| `PA194Schematic` | Independent of the other modules; it imports only Foundation. `boxL ar`: a language of `m` predicate letters of arities `ar`, without function symbols. `inst σ φ`: the internal formula of an arbitrary language `L` obtained from a standard formula `φ` of `boxL ar` by putting the internal formula `σ i` (of arity `ar i`, possibly nonstandard) for the `i`-th letter. `inst_neg`, `inst_shift`, `inst_substs`, `inst_free`: it commutes with negation, with substitution of terms, and with shift and opening when the letters are shifted too. `instDer`: a standard derivation in pure logic of a sequent of `boxL ar` gives an internal derivation of its instance in every internal theory, for every `σ`. `inst_provable_of_valid`: by the completeness theorem, every instance of a sentence of `boxL ar` that holds in all structures is internally provable. `instS σ φ` is the same instance for a formula `φ` without free variables, with its own equations (`instS_rel`, `instS_all`, `instS_imp`, `instS_substs`, …) and `instS_provable_of_valid` in typed form. This is the tool intended for the fields of `NameFacts` in which value formulas of nonstandard terms are parameters: the first-order argument is made once, semantically, with letters for the value formulas and for the fixed formulas of the ordinal domain. It is applied in `PA194NameFactsProof`. |
| `PA194NameForms` | `termBShift_closed`: a term of arity zero is not changed by the shift of bound variables. `atom_one`, `atom_two_outer`, `atom_two_inner`, `atom_two_vars`: the translation of `x = s` and of `x = y` under one and two formula binders, for a bound naming variable and a term `s` of arity zero. `tr_nameAll`, `tr_uniq`, `tr_exName`: the three translated name formulas as explicit source codes, in which the terms occur only through `valBody s` at a bound variable; `eqForm a b` is `∃v∃w (a ∧ b ∧ orderIso(v, w))`. These are identities between codes; no field of `NameFacts` is proved. |
| `PA194NameSchema` | `Letter`: predicate letters for the domain, source equality, order isomorphism, zero, successor, addition, multiplication, and four value letters. Closed standard formulas over them: `sNameAll`, `sUniq`, `sExName`, `sEqVal` and the value schemas `sZeroV`, `sSuccV`, `sAddV`, `sMulV`. Their typed internal mirrors `tNameAll`, … and the assignment `sig A` (typed quotes of the source templates; `A i` for the value letters), with `instS (sig A) (sX …) = tX …`. `tNameAll_tr`, `tUniq_tr`, `tExName_tr`, `tEqVal_tr`, `tSuccV_val`, `tAddV_val`, `tMulV_val`, `tZeroV_val`: the typed formulas have the codes of the translated name formulas and of `valBody` when their arguments have the codes `valBody s`. |
| `PA194NameSemantics` | For a structure `M` of the language of the letters: the letters as relations (`mD`, `mE`, `mI`, …), the meaning of each schema (`ev_sNameAll`, `ev_sUniq`, `ev_sExName`, `ev_sEqVal`, `wOf_sSuccV`, …), the twelve fixed hypotheses as sentences `sE1`, …, `sM2` with `MTheta M` and `ev_sWith`, and the facts about names as statements about relations on a set, proved directly: `m_atomTransfer`, `m_nSucc`, `m_nAdd`, `m_nMul`, `m_uZero`, `m_uSucc`, `m_uAdd`, `m_uMul`, `m_eZero`, `m_eSucc`, `m_eAdd`, `m_eMul`, `m_nameOfUniq`, `m_nameOfEq`. Nothing here mentions internal syntax. |
| `PA194NameFactsProof` | Sixteen closed sentences `fRefl`, …, `fEMul` and their validity under the twelve hypotheses in every structure. `valBody_split`: every value formula is the domain formula at its variable in conjunction with a remainder, so a value letter can stand for the remainder. `SourceFacts T`; `with_facts`: every instance of a sentence valid under the hypotheses is provable in `T`. `pair_of_ei`: the instance of `sEI` at a variable `&c`, by one internal specialization. `gd0`–`gd3`: from a provable implication to the guarded sequent. `field_nRefl`, …, `field_eMul`, and `nameFacts_of_sourceFacts : SourceFacts T → (∀ i, GDerivable T {tr (exName &i)}) → NameFacts T`, `termFacts_of_sourceFacts`. |
| `PA194InductionForms` | `trBody_or`, `trBody_neg`, `trBody_shift`. `allNames t p` (every name of `t` satisfies `p`) with `tr_allNames`, and `leibnizAll`: from `TermFacts T`, a guarded derivation of `tr (p[t]) → tr (allNames t p)`; the universally closed form of `leibniz`. `indBody p`, the induction axiom for `p` before the closure of its parameters, with `tr_indBody` and `free_substs1_succVar`. `tr_close_step`: from a guarded derivation of `tr (free b)` to one of `tr (∀ b)`. |
| `PA194InductionSchema` | The sentence `fInd` over the letters `Q` (translation of `p`) and `QS` (translation of `p[S x]`): ordinal induction for `Q`, "names of zero satisfy `Q`", "if `QS x` then names of the successor of `x` satisfy `Q`" and `∀x (Q x → QS x)` give `∀x Q x`; `valid_ind`. `indCode q`: the ordinal induction statement of the source theory for an internal property `q`. `v_ind`, `v_hbase`, `v_x2`, `v_concl`, `instS_sHstep`, `tXs_free`: the instances as codes. `step_derivable`: the step hypothesis, by `leibnizAll` at `S(&0)` and one relativized universal introduction. `induction_body : TermFacts T → SourceFacts T → (∀ q, IsSemiformula SourceL 1 q → Provable T (indCode q)) → IsSemiformula language 1 p → GDerivable T {tr (indBody p)}`. |
| `PA194ArithFacts` | Guarded derivations of the translations of four open formulas. `cong_add`, `cong_mul`: `s₁ = s₁' → s₂ = s₂' → s₁ + s₂ = s₁' + s₂'` and the same for `·`, for arbitrary internal terms, from `SourceFacts T`. `addSucc_open`: `S(&a) + &b = S(&a + &b)`, and `mulSucc_open`: `S(&a) · &b = &b + &a · &b`, from `SourceFacts T` and the further fixed facts `sA3`, `sM3`. `ne_derivable`: under the domain guard of `&c`, the value formula of the variable `&c` has a member. Sentences `fCAdd`, `fCMul`, `fAddSucc`, `fMulSucc` with their validity, and the relational lemmas `m_cAdd`, `m_cMul`, `m_addSucc`, `m_mulSucc`. |
| `PA194FixedAxiomQuotes` | Imports `PA194PAeqTargetInventory`. `q_eq`, `q_add`, `q_mul`, `q_succ`, `q_implies`: quotes of the standard syntax of the arithmetic language as the codes used here. `tr_close_quote`: closing one standard quantifier. `addCongruence_tr`, `mulCongruence_tr`, `addSucc_tr`, `mulSucc_tr`: `GDerivable T {tr ⌜σ⌝}` for the four quoted axioms. |
| `PA194GuardedClosed` | `discharge_step_of_shift`, `gd_provable_of_shift`: a guarded derivation of a formula that is not changed by the shift of free variables is a proof, when `T` proves that the domain is inhabited; the argument of `discharge_guards` with an arbitrary such formula in place of `⊥`. `tr_provable_of_closed`: the same for `tr φ` with `φ` invariant under shift. `addCongruence_provable`, `mulCongruence_provable`, `addSucc_provable`, `mulSucc_provable`: `Provable T (tr ⌜σ⌝)`. |
| `PA194InductionWiring` | `indBody_valid`. `tr_close_iter`: for a `Σ₁` iteration `cl` of a binder `B` that inverts opening, a guarded derivation of `tr φ` gives one of `tr (cl n φ)` for every internal `n`, by `Σ₁` induction on `n`. `induction_closed`, `induction_closed_provable`: the translated induction axiom with `n` parameters closed. `indCode_quotes`: `indCode q` in terms of the quotes of `Ordinal.domain`, `Ordinal.zero` and `Ordinal.successor` at bound variables. |
| `PA194SuccessorLaws` | The sentences `sAP`, `sMP`, `sAC` over the letters and their meaning in a structure (`ev_sAP`, `ev_sMP`, `ev_sAC`); `m_a3`, `m_m3`: the two successor facts follow from them under the twelve hypotheses; `a3_of_predecessor`, `m3_of_predecessor`: the corresponding internal proofs of `tHyp sA3` and `tHyp sM3`. |
| `PA194SemanticSupply` | Imports `PA194TypedTheory` and `PA194AdjunctiveFullSep`. `letterStructure`, `eval_sinst`, `sinst_closed`, `tau0_closed`; `source_supply`: a fixed hypothesis `tHyp φ` is internally provable in `adjunctiveFullSepTheory` if `φ` holds in the letter structure of every structure with equality that satisfies weak adjunction and all separation instances. |
| `PA194OrdinalInductionLink` | For models of the candidate PRA presentation, as in `pa194-model-axioms`. Imports `PA194UniformOrdinalFullSource` and `PA194SourceInhabited`. `ordinalInductionCode_eq : ordinalInductionCode q = indCode q`; `indCode_provable`: `adjunctiveFullSepTheory` proves `indCode q` for every internal property `q`; `induction_supplier_fullSource`: the induction supplier `hind` for that theory from its `TermFacts` and `SourceFacts`. |
| `PA194InductionSupplier` | Imports `PA194PAeqClosedInduction`, `PA194PAeqOpeningFormulaInverse` and `PA194ClosedSentenceEnvironment`. `inductionBody_eq : inductionBody p = indBody p`. `closedInduction_tr_provable`: `Provable T (tr (closedInduction p))`, by `induction_closed_provable` with `close` and `bindFormula 0`. `induction_supplier`: the same at `rootParameters`, by `sentence_root_packet`. |

All statements are for an arbitrary model `V` of `𝗜𝚺₁`, arbitrary `Δ₁` theories `U` and `T`
of the two languages, and internally valid codes that may be nonstandard.

## What is open

`OrdinaryCompiler` follows from `Interpretation ordinaryPAeq adjunctiveFullSepTheory` in every
model. Of its three fields, `inhabited` is proved for these theories in `pa194-model-logic`
(see the last item); `witness` and `axioms` are not.

- `witness`, the existential introduction at a function term, is reduced to `TermFacts T`
  (`witness_of_termFacts`) and that to `NameFacts T` (`termFacts_of_nameFacts`). Each of
  the seventeen fields of `NameFacts` is a guarded derivation of the
  translation of a formula that `ordinaryPAeq` proves, with `s, s', …` arbitrary internal
  terms of arity zero:
  - `nRefl`: `nameAll s s`;
  - `atomTransfer`: `nameAll s₁ s₁' → nameAll s₂ s₂' → s₁ = s₂ → s₁' = s₂'`;
  - `nameOfUniq`: `uniq t → &c = t → nameAll t &c`, and `nameOfEq`: `&c = t → nameAll &c t`;
  - `nSucc`, `nAdd`, `nMul`: `nameAll` passes through one function symbol;
  - `uVar`, `uZero`, `uSucc`, `uAdd`, `uMul`: `uniq` for a variable and for zero, and through
    one function symbol;
  - `eVar`, `eZero`, `eSucc`, `eAdd`, `eMul`: the same for `exName`.

  `nameFacts_of_sourceFacts` (`PA194NameFactsProof`) proves all seventeen from
  `SourceFacts T` and the field `eVar`, for any `T`. `SourceFacts T` says that `T` proves,
  internally, twelve fixed closed formulas, each the instance of a sentence over predicate
  letters at the quoted source templates (`tHyp`):
  - `sE1`: source equality is reflexive;
  - `sEI`: two members of the domain equal to the same thing are order-isomorphic;
  - `sIs`, `sIt`: order isomorphism is symmetric and transitive on the domain;
  - `sZ1`, `sZ2`: the domain has a zero, and any two zeros of it are isomorphic;
  - `sS1`, `sS2`: every member of the domain has a successor in it, and successors of
    isomorphic members are isomorphic;
  - `sA1`, `sA2`, `sM1`, `sM2`: the same for sums and products of two members.

  Each `tHyp s…` is the typed quote of an explicit standard formula of the source language,
  `sinst tau0 s…`: the sentence with the source templates substituted for its letters
  (`tHyp_eq_quote`, from `quote_sinst` of `PA194Schematic`). So `SourceFacts T` follows from
  `Provable T ⌜sinst tau0 s…⌝` for the twelve sentences (`sourceFacts_of_quotes`).

  `SourceFacts adjunctiveFullSepTheory` is not proved: internal provability of those twelve
  quotes in the actual source theory is missing. It would follow from standard derivations
  of the twelve formulas in that theory; none is supplied here. Independently of this, `pa194-model-axioms` proves six of the seventeen fields
  directly for the actual source theory and assumes the other eleven
  ([`NAME-FACTS-ELEVEN.md`](../pa194-model-axioms/NAME-FACTS-ELEVEN.md)); those eleven are
  among the fields that `nameFacts_of_sourceFacts` derives.
- `axioms`: a guarded proof of the translation of each fixed axiom of `ordinaryPAeq` and of
  each closed induction instance. `pa194-model-logic` works on these under `rootParameters`.
  For a sentence that translation should equal `tr`, by `formula_ext` restricted to formulas
  without free variables; that lemma is not written.

  For the induction instances, `induction_body` (`PA194InductionSchema`) derives, for every
  internal formula `p` of arity one (possibly nonstandard, with parameters) and any `T`,
  the translation of `indBody p`, which is `p[0] → (∀x (p → p[S x]) → ∀x p)`. Its inputs
  are `TermFacts T`, `SourceFacts T`, and `Provable T (indCode q)` for every internal source
  formula `q` of arity one, where `indCode q` is the ordinal induction statement of the
  source theory for the property `q`. `tr_close_step` (`PA194InductionForms`) passes a
  guarded derivation of `tr (free b)` to one of `tr (∀ b)`, the step that closes one
  parameter. `PA194InductionWiring` iterates it: `tr_close_iter` and `induction_closed` hold
  for any `Σ₁` function `cl` with `cl 0 φ = φ` and `cl (n+1) φ = ∀ (B (cl n φ))`, where `B`
  returns a formula of arity one that opens to its argument; `induction_closed_provable`
  adds that the result is a proof when it is invariant under shift and the domain is
  inhabited. `indCode_quotes` writes `indCode q` with the quotes of the standard `domain`,
  `zero` and `successor` formulas.

  `PA194InductionSupplier` imports the arithmetic development and states the result in its
  terms: `induction_supplier` proves
  `Provable T (translateFormula (rootParameters (closedInduction p)) (closedInduction p))`
  for every internal `p` of arity one, which is the hypothesis `hind` of
  `refutation_of_remaining` in `pa194-model-logic` for an arbitrary `T`. Its inputs are
  `TermFacts T`, `SourceFacts T`, `Provable T (indCode q)` for every internal `q`, and
  inhabitation of the domain.

  `PA194OrdinalInductionLink` supplies the last two for the actual source theory, in every
  model of the candidate PRA presentation whose arithmetic reduct satisfies `IΣ₁`:
  `ordinalInductionCode_eq` identifies `ordinalInductionCode` of `pa194-model-axioms` with
  `indCode`, `indCode_provable` is `fullSourceOrdinalProof` in that form, and
  `induction_supplier_fullSource` is `hind` for `adjunctiveFullSepTheory` from
  `TermFacts` and `SourceFacts` of that theory. Those two hypotheses are not proved here.

  For four of the fixed axioms, `PA194FixedAxiomQuotes` gives guarded derivations of
  `tr ⌜σ⌝` for the quoted sentences themselves: `addCongruence_tr` and `mulCongruence_tr`
  from `SourceFacts T`, and `addSucc_tr`, `mulSucc_tr` from `SourceFacts T` and one more
  fixed fact each, `T ⊢ tHyp sA3` and `T ⊢ tHyp sM3` (`PA194ArithFacts`): if `u'` is a
  successor of `u`, `w` a sum of `u'` and `v`, `w₀` a sum of `u` and `v` and `w₁` a successor
  of `w₀`, then `w` and `w₁` are order-isomorphic; and the same with products for `w`,
  `w₀` and a sum of `v` and `w₀` for `w₁`. These four are the fixed axioms that the
  supplier of `pa194-model-logic` still assumes
  ([`FORWARD-FIXED-FOUR.md`](../pa194-model-logic/FORWARD-FIXED-FOUR.md)); that supplier
  takes them as unguarded proofs of the quote of the standard translation.
  `PA194GuardedClosed` removes the guards: `gd_provable_of_shift` turns a guarded derivation
  of a formula invariant under shift into a proof, given that the domain is inhabited, and
  `addCongruence_provable`, `mulCongruence_provable`, `addSucc_provable`,
  `mulSucc_provable` state `Provable T (tr ⌜σ⌝)`. The identification of `tr ⌜σ⌝` with the
  quote of the standard translation used by that supplier is proved by
  `PA194RemainingFixedSupplier.tr_closed_quote`. The [conditional assembly](REFUTATION-TO-SCHEDULER.md)
  connects these four axioms and the ordinal induction supplier to refutation
  transport and modeled scheduler halting. The actual source proofs of `sA3` and
  `sM3` remain open.

  `PA194SuccessorLaws` reduces `sA3` and `sM3` to statements that follow the definition of
  the addition and multiplication traces: `sAP` (if `u` is a successor of `t` and `o` a sum
  of `u` and `b`, some member `d` of the domain is a sum of `t` and `b` and has `o` as a
  successor; the shape of `addPredecessorResult` of the relational source development),
  `sMP` (the same for products, with `o` a sum of `d` and `b`; `mulPredecessorResult`) and
  `sAC` (sums of `a, b` and of `b, a` are isomorphic). `a3_of_predecessor` derives `sA3`
  from `SourceFacts T` and `sAP`; `m3_of_predecessor` derives `sM3` from `SourceFacts T`,
  `sMP` and `sAC`. Of the three, `sAP` and `sMP` are proved for the actual source theory in
  [`pa194-source-semantics`](../pa194-source-semantics/README.md); `sAC` is not.
- A second way to supply fixed facts. Every fixed hypothesis here is the typed quote of a
  standard sentence of the source language, `tHyp φ = ⌜sinst tau0 φ⌝`. `PA194SemanticSupply`
  proves `source_supply`: `adjunctiveFullSepTheory.internalize V ⊢ tHyp φ` holds in every
  model `V` of `IΣ₁` if `φ` is true in the letter structure of every nonempty structure `N`
  of the relational source language in which equality is equality, weak adjunction holds,
  and every separation instance holds at every assignment of its parameters. It uses the
  completeness theorem, the first derivability condition, the characterization
  `fullSepTheory_mem_iff_typed` of the separation theory, `eval_sinst` (truth of a standard
  instance is truth in the structure whose letters are the relations defined by the
  standard formulas) and `sinst_closed`. So a fixed fact can be proved as a statement about
  such structures, with no derivation written.
  [`pa194-source-semantics`](../pa194-source-semantics/README.md) proves `sAP` and `sMP`
  this way.
- `inhabited` for the actual source theory is proved outside this directory
  (`PA194SourceInhabited.inhabited_provable` in `pa194-model-logic`), from the standard
  derivation of the empty-set formula.

Nothing here yields a consistency implication.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check.sh
```

runs [`check_bridge.py`](../pa194-model-fairness/check_bridge.py) with each module as the top
module, passing its arguments on (for example `--out DIR` to reuse compiled objects). On
2026-11-15 the nine modules were compiled directly with `lean`, in dependency order, against
objects of the standalone modules they import (the import closure of
`PA194ConditionalRefutation` and `PA194OrderIsoRew`, compiled from the repository sources at
`34c4c35edc`). The forty axiom reports are `[propext, Classical.choice, Quot.sound]`.
`PA194Schematic` was compiled the same day against the Foundation objects alone, and
`PA194NameForms` against the objects of the nine; their ten and six reports are the same
three axioms. `PA194NameSchema`, `PA194NameSemantics` and `PA194NameFactsProof` were compiled
the same way, on top of those; of their eight, nine and seventeen reports, the six for the
facts about relations in `PA194NameSemantics` list `propext` alone and the others the same
three axioms. `PA194InductionForms` and `PA194InductionSchema` were compiled the same way;
their seven and nine reports are the same three axioms. So were `PA194ArithFacts` and
`PA194FixedAxiomQuotes` (nine and six reports, the same three axioms), the latter also
against a locally compiled `PA194PAeqTargetInventory`, `PA194SuccessorLaws` (six reports;
`m_a3` and `m_m3` use `propext` only, the other four the same three axioms),
`PA194SemanticSupply` (four reports, the same three axioms; five of its imports from
`pa194-model-axioms` and `pa194-model-logic` were compiled locally for it),
`PA194OrdinalInductionLink` (three
reports, the same three axioms; its imports from `pa194-model-axioms` and `pa194-model-logic`
were compiled locally from the repository sources, 211 modules), `PA194InductionSupplier` (three
reports, the same three axioms; its imports from `pa194-model-logic` were compiled locally
from the repository sources, 448 modules of which most objects already existed),
`PA194InductionWiring` (five reports,
the same three axioms), and `PA194GuardedClosed` (six reports,
the same three axioms). The script itself has not been run.

Two incremental replays against the repository sources were made for an earlier state of this
directory, before `PA194GuardedCalculus` and `PA194TrCompile` existed and while the compiler
had a fixed guard bound (modules `PA194GuardedCompile`, `PA194TranslateShift`,
`PA194TranslateSubst`, `PA194GuardedEndpoint`, and then `PA194TranslateExt`).

- The first, after the shared PairGraph syntax change, rebuilt `PA194ConditionalRefutation`
  and those four modules, reported the twenty axiom audits they had then, and found no
  `sorryAx`. The dispatcher, sequent, Foundation and other listed overlays were prebuilt, so
  it was not a clean transitive build.
- The second rebuilt `PA194TranslateExt` against the result of the first; its seven axiom
  reports passed with no `sorryAx`, with transitive dependencies prebuilt.

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-incremental.sh "$PWD" NEW_EMPTY_OUTPUT
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-translate-ext.sh "$PWD" NEW_EMPTY_OUTPUT
```

`check-incremental.sh` now lists the current twenty modules with their report counts, because
`PA194GuardedEndpoint` no longer exists. In that form it has not been run. It writes
`PA194TranslateExt` into its output directory, so `check-translate-ext.sh` is only needed to
replay that module alone.

An incremental repository-source replay of the six modules through `PA194TrCompile`
passed on 2026-11-15, with 26 expected axiom reports and no `sorryAx`. A separate
incremental replay of `PA194Leibniz` against those objects passed with four axiom
reports and no `sorryAx`. The dispatcher, source theory and other listed overlays
were prebuilt; these checks do not rebuild the full transitive dependency closure.
The first replay used the preceding six-module version of `check-incremental.sh`;
the current twenty-module script has not been run as a whole. To replay the later
module alone against the same checked staged dependencies:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-leibniz.sh "$PWD" NEW_EMPTY_OUTPUT
```

A separate incremental repository-source replay of `PA194TermNames` against the
checked calculus and Leibniz objects passed with four axiom reports and no
`sorryAx`. Earlier source, dispatcher and other dependencies were prebuilt; this
is not a full transitive rebuild. Reproduce with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-term-names.sh "$PWD" NEW_EMPTY_OUTPUT
```

A separate incremental repository-source replay of `PA194ValueBody` against the
checked calculus and naming modules passed with six axiom reports and no
`sorryAx`. Earlier source and dispatcher dependencies were prebuilt; this is not
a full transitive rebuild. Reproduce with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-value-body.sh "$PWD" NEW_EMPTY_OUTPUT
```

A prior incremental replay of `PA194Schematic` passed six axiom audits. After
the sentence-layer update, a fresh incremental replay of `PA194Schematic` and
`PA194NameForms` passed nine and six audits respectively, with no `sorryAx`.
Their Foundation dependencies were prebuilt, so this is not a full transitive
rebuild. The standalone schematic checker now targets the current ten reports. Reproduce with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-schematic.sh "$PWD" NEW_EMPTY_OUTPUT
```

The updated schematic and name-form modules can be replayed together with a
fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-name-forms.sh "$PWD" NEW_EMPTY_OUTPUT
```

After the standard-quote extension, a repository-source replay rebuilt
`PA194Schematic`, `PA194NameForms`, `PA194NameSchema`, `PA194NameSemantics`
and `PA194NameFactsProof` in order, passing their ten, six, eight, nine and
seventeen axiom audits without `sorryAx`. Earlier dependencies remain prebuilt;
this is not a full transitive rebuild. The result derives the naming fields from
the twelve explicit `SourceFacts` and variable-name existence, which remain
assumptions of the generic theorem. Reproduce with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-name-facts.sh "$PWD" NEW_EMPTY_OUTPUT
```

An independent repository-source replay of `PA194InductionForms` and
`PA194InductionSchema` passed their seven and nine axiom reports without
`sorryAx`, against the separately replayed naming modules and other prebuilt
dependencies. It does not rebuild their full transitive closure. The translated
induction-body theorem is conditional on `TermFacts`, `SourceFacts` and the
source ordinal-induction supplier; parameter closure and the compiler connection
remain open. Reproduce with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-induction-body.sh "$PWD" NEW_EMPTY_OUTPUT
```

A separate repository-source replay of `PA194ArithFacts` and
`PA194FixedAxiomQuotes` passed nine and six axiom reports without `sorryAx`,
against the independently replayed naming and induction objects plus other
prebuilt dependencies. It does not rebuild their full transitive closure. The
results retain `SourceFacts` and, for the successor axioms, the explicit `sA3`
and `sM3` recursion hypotheses. Reproduce with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-fixed-arithmetic.sh "$PWD" NEW_EMPTY_OUTPUT
```

A separate repository-source replay of `PA194GuardedClosed` passed six axiom
audits without `sorryAx` against the independently replayed fixed-arithmetic
modules and other prebuilt dependencies. Its closed-form guard elimination and
four resulting axiom proofs remain conditional on the documented source facts,
domain inhabitation, and, where applicable, the `sA3` or `sM3` recursion fact.
The bridge to the standard-translation supplier remains open. Reproduce with a
fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-guarded-closed.sh "$PWD" NEW_EMPTY_OUTPUT
```

A separate repository-source replay of `PA194InductionWiring` passed five axiom
audits without `sorryAx` against the independently replayed induction and closed
guard modules and other prebuilt dependencies. It proves conditional iteration
of parameter closure for arbitrary internal lengths; identifying the concrete
closure and binding operations, shift invariance of the fully closed axiom, and
the root-parameter supplier remains open. Reproduce with a fresh output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-guarded-compiler/check-induction-wiring.sh "$PWD" NEW_EMPTY_OUTPUT
```
