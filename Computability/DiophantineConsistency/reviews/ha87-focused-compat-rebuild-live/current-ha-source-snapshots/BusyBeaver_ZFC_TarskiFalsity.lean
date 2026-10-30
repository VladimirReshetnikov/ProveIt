import BusyBeaver.ZFC.Lukasiewicz

/-!
The machines' relative falsity `F = Rel(0,0)`.

The calibrated machines have no falsity constructor. Their negation is
`A → F` with `F = Rel(0,0)`, the code-1 atom `v0 ∈ v0`, and their existential
rows `rho6` and `rho1` are built from it. Under a binder of label 0 that atom
is captured, so `F` is not a closed falsity; it is false in every model of
irreflexivity `∀x ¬ x ∈ x`, which is why the comparison theories include IR.

`ThmG F Ax` is the machine row set with an arbitrary falsity formula `F`.
`ThmG (rel 0 0) Ax` is literally the machines' logical calculus. The results:

* `thm_tau`: replacing `⊥` by `F` maps every derivation of the genuine-bottom
  calculus `Thm` to a derivation of `ThmG F`;
* `alias_sound`: `ThmG (rel 0 0)` is sound for irreflexive models;
* `alias_complete`: for a `⊥`-free theory and target, validity in all
  irreflexive models implies derivability in `ThmG (rel 0 0)`. The comparison
  axiom IR is not needed as a row: its translation `∀0 (F → F)` is a theorem.
-/

namespace SetTheory.BusyBeaver.ZFC.Tarski

open NF

namespace NF

/-- Existential quantifier relative to a falsity formula. -/
def exF (F : NF) (i : Nat) (a : NF) : NF := imp (all i (imp a F)) F

end NF

/-- The machine rows with falsity formula `F`. -/
inductive ThmG (F : NF) (Ax : NF → Prop) : NF → Prop
  | ax {a : NF} : Ax a → ThmG F Ax a
  | mp {a b : NF} : ThmG F Ax (imp a b) → ThmG F Ax a → ThmG F Ax b
  | gen (i : Nat) {a : NF} : ThmG F Ax a → ThmG F Ax (all i a)
  | rho8 (c u a b : NF) : ThmG F Ax (luk c u a b)
  | rho2 (i : Nat) (b c : NF) : ThmG F Ax (imp (all i (imp b c)) (imp (all i b) (all i c)))
  | rho4 (i j : Nat) (c : NF) : ThmG F Ax (imp (all i (all j c)) (all j (all i c)))
  | rho6 (i : Nat) (b : NF) : ThmG F Ax (imp (NF.exF F i (all i b)) b)
  | rho1 (i j : Nat) : ThmG F Ax (NF.exF F i (NF.eq i j))
  | rho7 (a b c : Nat) : ThmG F Ax (imp (NF.eq c a) (imp (NF.eq c b) (NF.eq a b)))
  | rho5 (a b c : Nat) : ThmG F Ax (imp (NF.eq c a) (imp (rel c b) (rel a b)))
  | rho3 (a b c : Nat) : ThmG F Ax (imp (NF.eq a b) (imp (rel c a) (rel c b)))
  | vacRel (a b c : Nat) : c ≠ a → c ≠ b → ThmG F Ax (imp (rel a b) (all c (rel a b)))
  | vacEq (a b c : Nat) : c ≠ a → c ≠ b → ThmG F Ax (imp (NF.eq a b) (all c (NF.eq a b)))

/-- Replace the genuine falsity by `F`. -/
def tau (F : NF) : NF → NF
  | rel i j => rel i j
  | NF.eq i j => NF.eq i j
  | NF.bot => F
  | imp a b => imp (tau F a) (tau F b)
  | all i a => all i (tau F a)

def BotFree : NF → Prop
  | rel _ _ => True
  | NF.eq _ _ => True
  | NF.bot => False
  | imp a b => BotFree a ∧ BotFree b
  | all _ a => BotFree a

theorem tau_botFree (F : NF) : ∀ f : NF, BotFree f → tau F f = f
  | rel _ _, _ => rfl
  | NF.eq _ _, _ => rfl
  | NF.bot, h => h.elim
  | imp a b, h => by simp only [tau, tau_botFree F a h.1, tau_botFree F b h.2]
  | all i a, h => by simp only [tau, tau_botFree F a h]

/-- Every genuine-bottom derivation translates to a relative-falsity one. -/
theorem thm_tau (F : NF) {Ax : NF → Prop} {f : NF} (h : Thm Ax f) :
    ThmG F (fun g => ∃ a, Ax a ∧ tau F a = g) (tau F f) := by
  induction h with
  | ax h => exact .ax ⟨_, h, rfl⟩
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2
  | gen i _ ih => exact .gen i ih
  | rho8 c u a b => exact .rho8 _ _ _ _
  | rho2 i b c => exact .rho2 i _ _
  | rho4 i j c => exact .rho4 i j _
  | rho6 i b => exact .rho6 i _
  | rho1 i j => exact .rho1 i j
  | rho7 a b c => exact .rho7 a b c
  | rho5 a b c => exact .rho5 a b c
  | rho3 a b c => exact .rho3 a b c
  | vacRel a b c h1 h2 => exact .vacRel a b c h1 h2
  | vacEq a b c h1 h2 => exact .vacEq a b c h1 h2

/-- Discharging axioms that are themselves derivable. -/
theorem ThmG.elim {F : NF} {B Ax : NF → Prop} (hB : ∀ g, B g → ThmG F Ax g) {f : NF}
    (h : ThmG F B f) : ThmG F Ax f := by
  induction h with
  | ax h => exact hB _ h
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2
  | gen i _ ih => exact .gen i ih
  | rho8 => exact .rho8 ..
  | rho2 => exact .rho2 ..
  | rho4 => exact .rho4 ..
  | rho6 => exact .rho6 ..
  | rho1 => exact .rho1 ..
  | rho7 => exact .rho7 ..
  | rho5 => exact .rho5 ..
  | rho3 => exact .rho3 ..
  | vacRel a b c h1 h2 => exact .vacRel a b c h1 h2
  | vacEq a b c h1 h2 => exact .vacEq a b c h1 h2

theorem implicationalG (F : NF) (Ax : NF → Prop) : Lukasiewicz.Implicational NF.imp (ThmG F Ax) where
  mp := ThmG.mp
  rho8 := ThmG.rho8

/-! ## Soundness for irreflexive models -/

universe u
variable {V : Type u}

theorem sat_exF (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x) (e : Nat → V) (i : Nat) (a : NF) :
    Sat mem e (NF.exF (rel 0 0) i a) ↔ ∃ d, Sat mem (update e i d) a := by
  simp only [NF.exF, Sat]
  exact ⟨fun h => Classical.byContradiction fun hn => hirr _ (h fun d hd => absurd ⟨d, hd⟩ hn),
    fun ⟨d, hd⟩ h => absurd (h d hd) (hirr _)⟩

theorem alias_sound {Ax : NF → Prop} {mem : V → V → Prop} (hirr : ∀ x, ¬ mem x x)
    (hAx : ∀ a, Ax a → ∀ e : Nat → V, Sat mem e a) :
    ∀ {f : NF}, ThmG (rel 0 0) Ax f → ∀ e : Nat → V, Sat mem e f := by
  intro f hf
  induction hf with
  | ax h => exact hAx _ h
  | mp _ _ ih1 ih2 => exact fun e => ih1 e (ih2 e)
  | gen i _ ih => exact fun e d => ih _
  | rho8 c u a b =>
      exact soundness (Ax := fun _ => False) (mem := mem) (fun _ h => h.elim) (.rho8 c u a b)
  | rho2 i b c => exact fun e h1 h2 d => h1 d (h2 d)
  | rho4 i j c =>
      exact soundness (Ax := fun _ => False) (mem := mem) (fun _ h => h.elim) (.rho4 i j c)
  | rho6 i b =>
      intro e h
      obtain ⟨d, hd⟩ := (sat_exF mem hirr e i _).mp h
      have := hd (e i)
      have hh : update (update e i d) i (e i) = e := by
        funext n; by_cases hn : n = i <;> simp [update, hn]
      rwa [hh] at this
  | rho1 i j =>
      intro e
      rw [sat_exF mem hirr]
      refine ⟨e j, ?_⟩
      by_cases hij : j = i
      · subst hij; simp [Sat, update]
      · simp [Sat, update, hij]
  | rho7 a b c =>
      exact soundness (Ax := fun _ => False) (mem := mem) (fun _ h => h.elim) (.rho7 a b c)
  | rho5 a b c =>
      exact soundness (Ax := fun _ => False) (mem := mem) (fun _ h => h.elim) (.rho5 a b c)
  | rho3 a b c =>
      exact soundness (Ax := fun _ => False) (mem := mem) (fun _ h => h.elim) (.rho3 a b c)
  | vacRel a b c h1 h2 =>
      exact soundness (Ax := fun _ => False) (mem := mem) (fun _ h => h.elim) (.vacRel a b c h1 h2)
  | vacEq a b c h1 h2 =>
      exact soundness (Ax := fun _ => False) (mem := mem) (fun _ h => h.elim) (.vacEq a b c h1 h2)

/-! ## Completeness with the relative falsity -/

/-- Irreflexivity as a genuine-bottom formula. -/
def irr : NF := all 0 (neg (rel 0 0))

theorem alias_complete {Ax : NF → Prop} (hbf : ∀ a, Ax a → BotFree a) {f : NF} (hf : BotFree f)
    (hval : ∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
      (∀ a, Ax a → ∀ e : Nat → D, Sat mem e a) → ∀ e : Nat → D, Sat mem e f) :
    ThmG (rel 0 0) Ax f := by
  let Ax' : NF → Prop := fun g => Ax g ∨ g = irr
  have hT : Thm Ax' f := by
    apply complete f
    intro D mem hAx' e
    have hirr : ∀ x, ¬ mem x x := by
      intro x hx
      have := hAx' irr (Or.inr rfl) (fun _ => x) x
      simp only [neg, Sat, update] at this
      exact this hx
    exact hval D mem hirr (fun a ha => hAx' a (Or.inl ha)) e
  have hG := thm_tau (rel 0 0) hT
  rw [tau_botFree _ f hf] at hG
  apply ThmG.elim _ hG
  rintro g ⟨a, ha, rfl⟩
  rcases ha with ha | rfl
  · rw [tau_botFree _ a (hbf a ha)]; exact .ax ha
  · -- τ(∀0 ¬ 0∈0) = ∀0 (F → F), a generalized identity.
    have k := Lukasiewicz.k (implicationalG (rel 0 0) Ax)
    have s := Lukasiewicz.s (implicationalG (rel 0 0) Ax)
    have id : ThmG (rel 0 0) Ax (imp (rel 0 0) (rel 0 0)) :=
      .mp (.mp (s (rel 0 0) (imp (rel 0 0) (rel 0 0)) (rel 0 0))
        (k (rel 0 0) (imp (rel 0 0) (rel 0 0)))) (k (rel 0 0) (rel 0 0))
    exact .gen 0 id

end SetTheory.BusyBeaver.ZFC.Tarski
