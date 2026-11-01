import ZFCinPA.LIterate

set_option autoImplicit false
noncomputable section

/-!
# Closure points of the reflection function, in template models

`LIterate.orbit_closure` builds a limit closed under a class function from
explicit separation and replacement resources. Here the class function is the
placeholder `F₅` of the six-placeholder language, and the resources are
discharged by `LTemplate.sep_iff`/`repl_iff` at concrete enlarged formulas:
`hstepS` (the inflationary step), `chainS` (chains from `α`), and the totalized
image and orbit relations. `closure_point`: in every template model, if `F₅`
is total on ordinals, then above every ordinal there is a nonzero limit closed
under `F₅`.
-/

namespace LeanProofs.ZFCinPA.LClosure

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate
open LeanProofs.ZFCinPA.EnvTransform LeanProofs.ZFCinPA.LPieces LeanProofs.ZFCinPA.LInvariant
open LeanProofs.ZFCinPA.LStepAnd LeanProofs.ZFCinPA.LStepBasic LeanProofs.ZFCinPA.LStepAtom
open LeanProofs.ZFCinPA.LIterate

local instance : Language.Mem L6 := ⟨Sum.inl Language.Set.Rel.mem⟩

/-! ## Pure pieces -/

section Pure

open SetTheory.BusyBeaver.ZFC.NamedZF SetTheory.BusyBeaver.ZFC.InternalRank

/-- `f` is a function with domain `d` (names `f = 0`, `d = 1`). -/
def funOnF : NForm :=
  .and (.all 2 (.all 3 (.all 4 (.imp (.and (pmemF 0 2 3) (pmemF 0 2 4)) (.eq 3 4)))))
    (.and (.all 2 (.imp (.mem 2 1) (.ex 3 (pmemF 0 2 3))))
      (.all 2 (.imp (.mem 2 0) (.ex 3 (.and (.mem 3 1) (.ex 4 (kpairF 2 3 4)))))))

def funOnP : SetTheorySemisentence 2 := piece 1 funOnF

/-- `⟨x, y⟩ ∈ f` (`f = #0`, `x = #1`, `y = #2`). -/
def pmemS : SetTheorySemisentence 3 := piece 2 (pmemF 0 1 2)

end Pure

section PureSemantics

open SetTheory.BusyBeaver.ZFC.NamedZF SetTheory.BusyBeaver.ZFC.InternalRank
  LeanProofs.BoundedZFCConsistency

variable {V : Type*} [SetStructure V] (H : _root_.SetTheory.ZFAxioms (memRel V)) (ε : Empty → V)

@[simp] theorem eval_pmemS (f x y : V) :
    pmemS.Eval ![f, x, y] ε ↔ _root_.SetTheory.kpair H x y ∈ f := by
  rw [pmemS, eval_piece, nsat_pmemF H]
  rfl

@[simp] theorem eval_funOnP (f d : V) : funOnP.Eval ![f, d] ε ↔ IsFunctionOn H f d := by
  rw [funOnP, eval_piece]
  simp only [funOnF, NSat, nsat_pmemF H, nsat_kpairF H]
  simp (disch := omega) only [upd_same, upd_other]
  simp only [IsFunctionOn]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨fun x y y' hy hy' => h₁ x y y' ⟨hy, hy'⟩, h₂, fun p hp => ?_⟩
    obtain ⟨x, hx, y, rfl⟩ := h₃ p hp
    exact ⟨x, y, hx, rfl⟩
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨fun x y y' h => h₁ x y y' h.1 h.2, h₂, fun p hp => ?_⟩
    obtain ⟨x, y, hx, rfl⟩ := h₃ p hp
    exact ⟨x, hx, y, rfl⟩

end PureSemantics

/-! ## Enlarged formulas -/

/-- `y = succ (x ∪ ⋃ F₅[x])`. -/
def hstepS : Semisentence L6 2 :=
  “x y. ∃ m, (∀ w, w ∈ m ↔ w ∈ x ∨ ∃ a, a ∈ x ∧ ∃ g, !F₅ a g ∧ w ∈ g) ∧ ∀ z, z ∈ y ↔ z ∈ m ∨ z = m”

/-- `f` is a chain of length `n + 1` from `α`. -/
def chainS : Semisentence L6 3 :=
  “α n f. (∃ s, !(lift succP) n s ∧ !(lift funOnP) f s) ∧
    (∃ e, (∀ w, w ∉ e) ∧ !(lift pmemS) f e α) ∧
    (∀ k, ∀ x, !(lift pmemS) f k x → !(lift ordP) x) ∧
    ∀ k, k ∈ n → ∀ x, ∀ y, !(lift pmemS) f k x →
      (∃ s, !(lift succP) k s ∧ !(lift pmemS) f s y) → !hstepS x y”

/-- Chains of length `n + 1` exist (`n` first, `α` second). -/
def chainExS : Semisentence L6 2 := “n α. ∃ f, !chainS α n f”

/-- Two functions agree at `k`. -/
def agreeS : Semisentence L6 3 :=
  “k f f'. ∀ x, ∀ x', !(lift pmemS) f k x → !(lift pmemS) f' k x' → x = x'”

/-- `F₅`, totalized by `∅` off the ordinals. -/
def imgS : Semisentence L6 2 := “a g. (!(lift ordP) a ∧ !F₅ a g) ∨ (¬!(lift ordP) a ∧ ∀ z, z ∉ g)”

/-- The `n`-th orbit point, totalized by `∅` off `ω`. -/
def orbS : Semisentence L6 3 :=
  “n γ α. (!(lift natP) n ∧ ∃ f, !chainS α n f ∧ !(lift pmemS) f n γ) ∨
    (¬!(lift natP) n ∧ ∀ z, z ∉ γ)”

/-! ## Readings and the closure point -/

section Readings

open SetTheory.BusyBeaver.ZFC.InternalOrd LeanProofs.BoundedZFCConsistency

variable {M : Type} [Nonempty M] [SetStructure M] [Structure L6 M] [Structure.Eq L6 M]
  [Structure.Mem L6 M] [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)]

local notation "HM" => ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)

/-- The placeholder function, as a relation. -/
abbrev F5 (a g : M) : Prop := F₅.Eval ![a, g] Empty.elim

omit [Nonempty M] [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)] in
theorem eval_hstepS (x y : M) : hstepS.Eval ![x, y] Empty.elim ↔ HStep F5 x y := by
  simp [hstepS, HStep]

omit [Structure L6 M] [Structure.Eq L6 M] [Structure.Mem L6 M] in
theorem empty_iff (e : M) : (∀ w, w ∉ e) ↔ e = _root_.SetTheory.vempty HM :=
  ⟨fun h => _root_.SetTheory.ZFAxioms.ext HM _ _ fun z => ⟨fun hz => absurd hz (h z),
      fun hz => absurd hz (_root_.SetTheory.vempty_spec HM z)⟩,
    fun h w hw => _root_.SetTheory.vempty_spec HM w (h ▸ hw)⟩

theorem eval_chainS (α n f : M) : chainS.Eval ![α, n, f] Empty.elim ↔ Chain HM F5 α n f := by
  simp only [chainS, Chain]
  simp [eval_succP HM, eval_funOnP HM, eval_pmemS HM, eval_hstepS, empty_iff]

omit [M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory)] in
theorem eval_imgS (a g : M) :
    imgS.Eval ![a, g] Empty.elim ↔
      (Ord (memRel M) a ∧ F5 a g) ∨ (¬ Ord (memRel M) a ∧ ∀ z, z ∉ g) := by
  simp [imgS]

theorem eval_chainExS (n α : M) :
    chainExS.Eval ![n, α] Empty.elim ↔ ∃ f, Chain HM F5 α n f := by
  simp [chainExS, eval_chainS]

theorem eval_agreeS (k f f' : M) :
    agreeS.Eval ![k, f, f'] Empty.elim ↔
      ∀ x x', _root_.SetTheory.kpair HM k x ∈ f → _root_.SetTheory.kpair HM k x' ∈ f' → x = x' := by
  simp [agreeS, eval_pmemS HM]

theorem eval_orbS (n γ α : M) :
    orbS.Eval ![n, γ, α] Empty.elim ↔
      (n ∈ _root_.SetTheory.omegaV HM ∧ ∃ f, Chain HM F5 α n f ∧ _root_.SetTheory.kpair HM n γ ∈ f) ∨
      (n ∉ _root_.SetTheory.omegaV HM ∧ ∀ z, z ∉ γ) := by
  simp [orbS, eval_natP HM, eval_chainS, eval_pmemS HM]

end Readings

section Closure

open SetTheory.BusyBeaver.ZFC.InternalOrd LeanProofs.BoundedZFCConsistency

variable {M : Type} [Nonempty M] [SetStructure M] [s : Structure L6 M] [Structure.Eq L6 M]
  [Structure.Mem L6 M] [M↓[L6] ⊧* templTheory 6 ar6]

/-- **Closure points exist**: in every template model, if `F₅` is a total
function on ordinals above its argument, then above every ordinal there is a
nonzero limit closed under `F₅`. -/
theorem closure_point :
    haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
    Tot (F5 (M := M)) → ∀ α : M, Ord (memRel M) α →
      ∃ β, IsLim (memRel M) β ∧ α ∈ β ∧ ∀ a, a ∈ β → ∀ g, F5 a g → g ∈ β := by
  haveI : M↓[ℒₛₑₜ] ⊧* (𝗭𝗙 : SetTheory) := pure_models (k := 6) (arities := ar6)
  intro htot α hα
  have hR := ConstructibleInterpretation.regular_of_modelsZF (V := M)
  set H := ConstructibleInterpretation.zfAxioms_of_modelsZF (V := M)
  -- the image of `F₅` on an ordinal
  have himg : ∀ x : M, Ord (memRel M) x → ∃ Y : M, ∀ g, g ∈ Y ↔ ∃ a, a ∈ x ∧ F5 a g := by
    intro x hx
    have hfun : ∀ a : M, ∃! g, imgS.Eval ![a, g] Empty.elim := by
      intro a
      by_cases ha : Ord (memRel M) a
      · obtain ⟨g, -, -, hFg, u⟩ := htot a ha
        refine ⟨g, (eval_imgS a g).2 (Or.inl ⟨ha, hFg⟩), fun g' hg' => ?_⟩
        rcases (eval_imgS a g').1 hg' with ⟨-, h⟩ | ⟨h, -⟩
        · exact u g' h
        · exact absurd ha h
      · refine ⟨_root_.SetTheory.vempty H,
          (eval_imgS a _).2 (Or.inr ⟨ha, fun z => _root_.SetTheory.vempty_spec H z⟩), fun g' hg' => ?_⟩
        rcases (eval_imgS a g').1 hg' with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd h ha
        · exact (empty_iff g').1 h
    obtain ⟨Y, hY⟩ := repl_iff (k := 6) (arities := ar6) (Rewriting.emb imgS) (fun _ => x)
      (by simpa using hfun) x
    refine ⟨Y, fun g => ?_⟩
    have hY' := hY g
    simp only [Semiformula.eval_emb] at hY'
    rw [hY']
    refine exists_congr fun a => and_congr_right fun hax => ?_
    rw [eval_imgS]
    have hao : Ord (memRel M) a := ord_of_mem hx hax
    exact ⟨fun h => h.elim (fun h => h.2) (fun h => absurd hao h.1), fun h => Or.inl ⟨hao, h⟩⟩
  -- separation: chains of length `n + 1` exist
  have hsepC : ∃ S : M, ∀ n, n ∈ S ↔ n ∈ _root_.SetTheory.omegaV H ∧ ∃ f, Chain H F5 α n f := by
    obtain ⟨S, hS⟩ := sep_iff (k := 6) (arities := ar6)
      ((Rewriting.emb chainExS : Semiproposition L6 2) ⇜ ![#0, &0]) (fun _ => α)
      (_root_.SetTheory.omegaV H)
    refine ⟨S, fun n => (hS n).trans (and_congr_right fun _ => ?_)⟩
    rw [← eval_chainExS]
    simp
  -- separation: two functions agree at `k`
  have hsepA : ∀ f f' : M, ∃ S : M, ∀ k, k ∈ S ↔ k ∈ _root_.SetTheory.omegaV H ∧
      ∀ x x', _root_.SetTheory.kpair H k x ∈ f → _root_.SetTheory.kpair H k x' ∈ f' → x = x' := by
    intro f f'
    obtain ⟨S, hS⟩ := sep_iff (k := 6) (arities := ar6)
      ((Rewriting.emb agreeS : Semiproposition L6 3) ⇜ ![#0, &0, &1])
      (fun i => if i = 0 then f else f') (_root_.SetTheory.omegaV H)
    refine ⟨S, fun k => (hS k).trans (and_congr_right fun _ => ?_)⟩
    rw [← eval_agreeS]
    simp
  -- replacement: the orbit
  have horb : ∀ n : M, ∃! γ, orbS.Eval ![n, γ, α] Empty.elim := by
    intro n
    by_cases hn : n ∈ _root_.SetTheory.omegaV H
    · obtain ⟨f, hf⟩ := chain_exists H hR htot himg hα hsepC n hn
      obtain ⟨γ, hγ⟩ := hf.1.2.1 n (_root_.SetTheory.vsucc_self H n)
      refine ⟨γ, (eval_orbS n γ α).2 (Or.inl ⟨hn, f, hf, hγ⟩), fun γ' hγ' => ?_⟩
      rcases (eval_orbS n γ' α).1 hγ' with ⟨-, f', hf', hγ'f⟩ | ⟨h, -⟩
      · exact chain_agree H hf' hf hn hn (hsepA f' f) n hn γ' γ hγ'f hγ
      · exact absurd hn h
    · refine ⟨_root_.SetTheory.vempty H,
        (eval_orbS n _ α).2 (Or.inr ⟨hn, fun z => _root_.SetTheory.vempty_spec H z⟩), fun γ' hγ' => ?_⟩
      rcases (eval_orbS n γ' α).1 hγ' with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hn
      · exact (empty_iff γ').1 h
  obtain ⟨O, hO⟩ := repl_iff (k := 6) (arities := ar6)
    ((Rewriting.emb orbS : Semiproposition L6 3) ⇜ ![#0, #1, &0]) (fun _ => α)
    (fun n => by simpa using horb n) (_root_.SetTheory.omegaV H)
  refine orbit_closure H hR htot himg hα hsepC hsepA (O := O) fun γ => ?_
  have hO' := hO γ
  simp only [Rewriting.subst, Semiformula.eval_substs] at hO'
  rw [hO']
  refine exists_congr fun n => ?_
  constructor
  · rintro ⟨hn, h⟩
    have h' : orbS.Eval ![n, γ, α] Empty.elim := by simpa using h
    rcases (eval_orbS n γ α).1 h' with ⟨-, hc⟩ | ⟨h, -⟩
    · exact ⟨hn, hc⟩
    · exact absurd hn h
  · rintro ⟨hn, hc⟩
    refine ⟨hn, ?_⟩
    have h' : orbS.Eval ![n, γ, α] Empty.elim := (eval_orbS n γ α).2 (Or.inl ⟨hn, hc⟩)
    simpa using h'

end Closure

end LeanProofs.ZFCinPA.LClosure
