import BusyBeaver.ZFC.KLowerTag
import BusyBeaver.ZFC.ProfileComposition
import BusyBeaver.ZFC.KQHyp

/-!
Coded bisimilarity on the tagged domain (Elliot Glazer's `KQuot`, `KQuotSym`, `KQuotTrans`,
`KQuotExt`), from the repository's profile lemmas.

The tagged domain has equality-free collection for every formula (`tag_gic`, from
`tag_collection`), transitive containers and exact pairs. That is all the profile lemmas need:
reflexivity (`bisim_refl_of_collection`), symmetry (`eqv_symm_of_instances`), and, through the
transitive-container lemmas of `ProfileComposition`, transitivity and extensionality of `Eqv`.
-/

namespace SetTheory.BusyBeaver.ZFC.KLower

open Form Profile ProfilePairs ProfileCollection ProfileComposition ProfileSyntax ProfileModel
open CompositionModel DeepPositiveClosure ProfileComposition

universe u
variable {V : Type u} {mem : V → V → Prop}

section Eqv

variable (hs : FormSeed mem) (hirr : ∀ x, ¬ mem x x) {t : V} (ht : ∀ z, ¬ mem z t)
include hs hirr ht

theorem tag_gic : ModelsGIC (tmem mem t) := by
  intro φ _ env
  rw [sat_gicForm]
  intro a
  obtain ⟨b, h1, h2⟩ := tag_collection hs hirr ht (rename swap01 φ) env a
  have hsw : ∀ x y, Sat (tmem mem t) (scons y (scons x env)) (rename swap01 φ) ↔
      MatrixRelation (tmem mem t) φ env x y := fun x y =>
    Sat_rename_ext _ _ _ _ fun n => by rcases n with _ | _ | n <;> rfl
  refine ⟨b, fun y hy => ?_, fun x hx ⟨y, hy⟩ => ?_⟩
  · obtain ⟨x, hx⟩ := h1 y hy
    exact ⟨x, (hsw x y).mp hx⟩
  · obtain ⟨z, hz, hxz⟩ := h2 x hx ⟨y, (hsw x y).mpr hy⟩
    exact ⟨z, hz, (hsw x z).mp hxz⟩

theorem tag_tc : TransContainers (tmem mem t) := tag_transitive hs hirr ht

theorem tag_pairs : ∀ a b : Tag mem t, ∃ p, Pair (tmem mem t) p a b := fun a b => by
  obtain ⟨p, hp⟩ := tag_pair hs hirr ht a b
  refine ⟨p, fun z => ⟨fun ⟨w, hw, hzw⟩ => ?_, fun h => ?_⟩⟩
  · rcases (hp w).mp hw with rfl | rfl
    · exact Or.inl hzw
    · exact Or.inr hzw
  · rcases h with h | h
    · exact ⟨a, (hp a).mpr (Or.inl rfl), h⟩
    · exact ⟨b, (hp b).mpr (Or.inr rfl), h⟩

theorem tag_codes : ∀ x y : Tag mem t, ∃ c, OrderedPair (tmem mem t) x y c :=
  orderedPairs_of_pairs _ (tag_pairs hs hirr ht)

theorem tag_refl (x : Tag mem t) : Eqv (tmem mem t) x x := by
  obtain ⟨d, hx, hd⟩ := tag_tc hs hirr ht x
  exact bisim_refl_of_collection _ x d hx hd (tag_codes hs hirr ht)
    (diagonal_instance _ (tag_gic hs hirr ht) d)

theorem tag_symm {x y : Tag mem t} (h : Eqv (tmem mem t) x y) : Eqv (tmem mem t) y x :=
  eqv_symm_of_instances _ (tag_codes hs hirr ht) (reverse_instance _ (tag_gic hs hirr ht)) h

theorem tag_trans {x y z : Tag mem t} (h1 : Eqv (tmem mem t) x y) (h2 : Eqv (tmem mem t) y z) :
    Eqv (tmem mem t) x z :=
  eqv_trans_of_instances _ (tag_tc hs hirr ht) (tag_codes hs hirr ht)
    (fiber_instance _ (tag_gic hs hirr ht)) (composition_instance _ (tag_gic hs hirr ht))
    (union_instance _ (tag_gic hs hirr ht)) h1 h2

theorem tag_ext (x y : Tag mem t) (h : ∀ z, Member (tmem mem t) z x ↔ Member (tmem mem t) z y) :
    Eqv (tmem mem t) x y :=
  eqv_extensionality_of_instances _ (tag_tc hs hirr ht) (tag_pairs hs hirr ht)
    (union_instance _ (tag_gic hs hirr ht)) (match_instance _ (tag_gic hs hirr ht))
    (backMatch_instance _ (tag_gic hs hirr ht)) (tag_refl hs hirr ht)
    (fun _ _ => tag_symm hs hirr ht) x y h

/-! ## Interpreted membership respects `Eqv` -/

theorem member_left {x x' y : Tag mem t} (hxx' : Eqv (tmem mem t) x x')
    (h : Member (tmem mem t) x y) : Member (tmem mem t) x' y := by
  obtain ⟨z, hz, hxz⟩ := h
  exact ⟨z, hz, tag_trans hs hirr ht (tag_symm hs hirr ht hxx') hxz⟩

theorem member_right {x y y' : Tag mem t} (hyy' : Eqv (tmem mem t) y y')
    (h : Member (tmem mem t) x y) : Member (tmem mem t) x y' := by
  obtain ⟨r, hr, hEdge⟩ := hyy'
  obtain ⟨z, hz, hxz⟩ := h
  obtain ⟨z', hz', hzz'⟩ := (hr y y' hEdge).1 z hz
  exact ⟨z', hz', tag_trans hs hirr ht hxz ⟨r, hr, hzz'⟩⟩

theorem member_raw {x y : Tag mem t} (h : tmem mem t x y) : Member (tmem mem t) x y :=
  ⟨x, h, tag_refl hs hirr ht x⟩

end Eqv

end SetTheory.BusyBeaver.ZFC.KLower
