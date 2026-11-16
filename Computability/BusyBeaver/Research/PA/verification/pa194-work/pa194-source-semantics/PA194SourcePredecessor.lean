import PA194SourceModelBase
import PA194SuccessorLaws
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The predecessor laws of addition and multiplication in the source theory

In a structure with equality that satisfies the separation instances:

* `restrict_graph`: for a graph `g` with domain `u ∪ {u}` and `u` a successor of `t`, the
  entries of `g` whose first component is in `t ∪ {t}` form a graph with domain `t ∪ {t}`
  (one separation instance, with `t` as parameter).
* `add_predecessor`: if `u` is a successor of the ordinal representative `t` and `o` a sum
  of `u` and `b`, then some ordinal representative `d` is a sum of `t` and `b` and has `o`
  as a successor. The trace of `u + b` gives `d` by its recurrence clause, and its
  restriction is a trace of `t + b`.
* `mul_predecessor`: the same for products, with `o` a sum of `d` and `b`.

`sAP_supply` and `sMP_supply` are the corresponding internal proofs in the adjunctive source
theory with full separation, in every model of `IΣ₁`, by `source_supply`.
-/
namespace PA194SourceModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194Schematic PA194GuardedCompiler
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal
open M6.PA.RelationalSource.PairGraph

attribute [local instance] PA194ModelLogic.sourceLanguageAdjTheory

section model
variable {N : Type} [s : Structure SourceL N] [Structure.Eq SourceL N]

/-- "A Kuratowski pair whose first component is a member of the parameter `&0` or equal to
it." -/
def restrictProp : Semiproposition SourceL 1 :=
  ∃⁰ ∃⁰ (PairGraph.kuratowski (.bvar 2) (.bvar 1) (.bvar 0) ⋏
    (mem (.fvar 0) (.bvar 1) ⋎ eq (.bvar 1) (.fvar 0)))

theorem eval_restrictProp (f : ℕ → N) (q : N) :
    FirstOrder.Semiformula.Eval (s := s) ![q] f restrictProp ↔
      ∃ x y : N, SKur q x y ∧ (Mem x (f 0) ∨ x = f 0) := by
  show se ![q] f restrictProp ↔ _
  simp [restrictProp]

variable (hsep : ∀ (p : Semiproposition SourceL 1) (f : ℕ → N),
  FirstOrder.Semiformula.Evalf (s := s) f (separationFormula p))
include hsep

theorem restrict_exists (g t : N) :
    ∃ g' : N, ∀ x y : N, SEdge g' x y ↔ (SEdge g x y ∧ (Mem x t ∨ x = t)) := by
  obtain ⟨g', hg'⟩ := sep_spec hsep restrictProp (fun _ => t) g
  refine ⟨g', fun x y => ?_⟩
  constructor
  · rintro ⟨p, hp, hk⟩
    obtain ⟨hpg, hP⟩ := (hg' p).mp hp
    obtain ⟨x', y', hk', hx'⟩ := (eval_restrictProp (fun _ => t) p).mp hP
    obtain ⟨e1, e2⟩ := kur_inj hk hk'
    subst e1
    exact ⟨⟨p, hpg, hk⟩, hx'⟩
  · rintro ⟨⟨p, hpg, hk⟩, hx⟩
    exact ⟨p, (hg' p).mpr ⟨hpg, (eval_restrictProp (fun _ => t) p).mpr ⟨x, y, hk, hx⟩⟩, hk⟩

theorem restrict_graph {t u g : N} (hs : SSucc t u) (hgd : SGraphDom u g)
    (hf : SFun g) (hr : SRange g) :
    ∃ g' : N, (∀ x y : N, SEdge g' x y ↔ (SEdge g x y ∧ (Mem x t ∨ x = t))) ∧
      (SGraphDom t g' ∧ (SFun g' ∧ SRange g')) := by
  obtain ⟨g', hg'⟩ := restrict_exists hsep g t
  refine ⟨g', hg', ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨y, h⟩
      exact ((hg' x y).mp h).2
    · intro hx
      obtain ⟨y, hy⟩ := (hgd x).mpr (Or.inl ((hs x).mpr hx))
      exact ⟨y, (hg' x y).mpr ⟨hy, hx⟩⟩
  · intro x y z ⟨h1, h2⟩
    exact hf x y z ⟨((hg' x y).mp h1).1, ((hg' x z).mp h2).1⟩
  · intro x y h
    exact hr x y ((hg' x y).mp h).1

/-- The zero of a trace with domain `u ∪ {u}` lies in `t ∪ {t}` when `u` is a successor of
`t`. -/
theorem zero_below {t u g e c : N} (hs : SSucc t u) (hgd : SGraphDom u g) (he : SZero e)
    (hbase : SEdge g e c) : Mem e t ∨ e = t := by
  rcases (hgd e).mp ⟨c, hbase⟩ with h | h
  · exact (hs e).mp h
  · have h1 : Mem t u := (hs t).mpr (Or.inr rfl)
    rw [← h] at h1
    exact absurd h1 (he t)

theorem add_predecessor {t u b o : N} (ht : SDom t) (hs : SSucc t u) (ha : SAdd u b o) :
    ∃ d : N, SDom d ∧ (SAdd t b d ∧ SSucc d o) := by
  obtain ⟨e, g, he, ⟨hgd, hf, hr, hbase, hrec⟩, hedge⟩ := ha
  obtain ⟨d, hd, hsd⟩ := hrec u o t ⟨hedge, hs⟩
  obtain ⟨g', hg', hgd', hf', hr'⟩ := restrict_graph hsep hs hgd hf hr
  have htt : STrans t := ht.1.1
  have het : Mem e t ∨ e = t := zero_below hsep hs hgd he hbase
  refine ⟨d, hr t d hd, ⟨e, g', he, ⟨hgd', hf', hr', (hg' e b).mpr ⟨hbase, het⟩, ?_⟩,
    (hg' t d).mpr ⟨hd, Or.inr rfl⟩⟩, hsd⟩
  intro a b' c ⟨hab, hca⟩
  obtain ⟨hab, hat⟩ := (hg' a b').mp hab
  obtain ⟨d', hd', hsd'⟩ := hrec a b' c ⟨hab, hca⟩
  have hc_in_a : Mem c a := (hca c).mpr (Or.inr rfl)
  have hct : Mem c t ∨ c = t := by
    rcases hat with h | h
    · exact Or.inl (htt a c ⟨h, hc_in_a⟩)
    · rw [h] at hc_in_a
      exact Or.inl hc_in_a
  exact ⟨d', (hg' c d').mpr ⟨hd', hct⟩, hsd'⟩

theorem mul_predecessor {t u b o : N} (ht : SDom t) (hs : SSucc t u) (hm : SMul u b o) :
    ∃ d : N, SDom d ∧ (SMul t b d ∧ SAdd d b o) := by
  obtain ⟨e, g, he, ⟨hgd, hf, hr, hbase, hrec⟩, hedge⟩ := hm
  obtain ⟨d, hd, hsd⟩ := hrec u o t ⟨hedge, hs⟩
  obtain ⟨g', hg', hgd', hf', hr'⟩ := restrict_graph hsep hs hgd hf hr
  have htt : STrans t := ht.1.1
  have het : Mem e t ∨ e = t := zero_below hsep hs hgd he hbase
  refine ⟨d, hr t d hd, ⟨e, g', he, ⟨hgd', hf', hr', (hg' e e).mpr ⟨hbase, het⟩, ?_⟩,
    (hg' t d).mpr ⟨hd, Or.inr rfl⟩⟩, hsd⟩
  intro a b' c ⟨hab, hca⟩
  obtain ⟨hab, hat⟩ := (hg' a b').mp hab
  obtain ⟨d', hd', hsd'⟩ := hrec a b' c ⟨hab, hca⟩
  have hc_in_a : Mem c a := (hca c).mpr (Or.inr rfl)
  have hct : Mem c t ∨ c = t := by
    rcases hat with h | h
    · exact Or.inl (htt a c ⟨h, hc_in_a⟩)
    · rw [h] at hc_in_a
      exact Or.inl hc_in_a
  exact ⟨d', (hg' c d').mpr ⟨hd', hct⟩, hsd'⟩

#print axioms add_predecessor
#print axioms mul_predecessor
end model

section supply
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] adjunctiveFullSepTheoryDelta

/-- The predecessor law of addition is internally provable in the source theory. -/
theorem sAP_supply :
    adjunctiveFullSepTheory.internalize V ⊢ (tHyp sAP : Bootstrapping.Semiformula V SourceL 0) := by
  apply source_supply
  intro N _ s _ _ hsep f
  refine (@ev_sAP N (sourceLetters s f)).mpr ?_
  intro t u b o dt _ _ _ st au
  obtain ⟨d, dd, ad, sd⟩ := add_predecessor hsep ((mD_iff f t).mp dt) ((mS_iff f t u).mp st)
    ((mA_iff f u b o).mp au)
  exact ⟨d, (mD_iff f d).mpr dd, (mA_iff f t b d).mpr ad, (mS_iff f d o).mpr sd⟩

/-- The predecessor law of multiplication is internally provable in the source theory. -/
theorem sMP_supply :
    adjunctiveFullSepTheory.internalize V ⊢ (tHyp sMP : Bootstrapping.Semiformula V SourceL 0) := by
  apply source_supply
  intro N _ s _ _ hsep f
  refine (@ev_sMP N (sourceLetters s f)).mpr ?_
  intro t u b o dt _ _ _ st mu
  obtain ⟨d, dd, md, ad⟩ := mul_predecessor hsep ((mD_iff f t).mp dt) ((mS_iff f t u).mp st)
    ((mMu_iff f u b o).mp mu)
  exact ⟨d, (mD_iff f d).mpr dd, (mMu_iff f t b d).mpr md, (mA_iff f d b o).mpr ad⟩

#print axioms sAP_supply
#print axioms sMP_supply
end supply
end PA194SourceModel
