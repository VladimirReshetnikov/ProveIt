import BusyBeaver.ZFC.Code254Models
import BusyBeaver.ZFC.NamedForm254
import BusyBeaver.ZFC.DecodeFresh254

/-!
An explicit sufficient native-model interface for the original decoded bundle.

Actual CP, GIC for every native Form and raw irreflexivity imply ModelsDecoded.
No native matrix is submitted to an equality-free-only GIC premise. The own-code
freshness lemma handles every natural code, including zero's truth alias.
The original c != a,b gates remain; a=b is handled separately by an empty image.
This does not transport IR through a quotient or assert a consistency endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.NativeDecoded254

open Tarski (NF update)
open Code254Containers ProfileCollection ProfileSyntax DeepPositiveClosure

universe u
variable {V : Type u}

/-- Full GIC ranges over actual native Form matrices, including equality. -/
def FullGIC (mem : V → V → Prop) : Prop :=
  ∀ phi env, SetTheory.Sat mem env (gicForm phi)

theorem matrix_instance (mem : V → V → Prop) (hG : FullGIC mem)
    (a b c : Nat) (e : Nat → V) :
    CollectionInstance mem (fun x y =>
      Tarski.Sat mem (update (update e a x) b y) (Code254.dec c)) := by
  exact ProfileModel.collectionInstance_congr mem _ _
    (NamedForm254.sat_matrix mem (Code254.dec c) a b e)
    ((sat_gicForm mem _ e).mp (hG (NamedForm254.matrix (Code254.dec c) a b) e))

/-- This is a semantic equality, not an enc(dec c)=c assertion. -/
theorem sat_dec_bundle_named (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (a b c : Nat) (e : Nat → V) :
    Tarski.Sat mem e (Code254.dec (Code254.bundle a b c)) ↔
      Tarski.Sat mem e (namedBundle a b c (Code254.dec c)) := by
  simp only [Code254.bundle, Code254.bundleC, Code254.bundleG,
    Code254.sat_wa mem hirr, Code254.sat_wex mem hirr,
    Code254.sat_wim, Code254.sat_wal, Code254.sat_wel, Code254.sat_weq,
    namedBundle, namedC, namedG, sat_conj mem hirr, sat_ex mem hirr, Tarski.Sat]

/-- All original C instances, with the a=b collision retained. -/
theorem namedC_of_containers (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hC : Containers mem) (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b)
    (e : Nat → V) : Tarski.Sat mem e (namedC a b c) := by
  obtain ⟨v, hav, hTrans, hPower⟩ := hC (e c)
  apply (sat_ex mem hirr e b _).mpr
  refine ⟨v, (sat_conj mem hirr _ _ _).mpr ⟨?_, ?_⟩⟩
  · intro x hx
    by_cases hab : a = b
    · subst b
      have hxx : mem x x := by simpa [Tarski.Sat, update] using hx
      exact (hirr x hxx).elim
    · have hxv : mem x v := by simpa [Tarski.Sat, update, Ne.symm hab] using hx
      apply (sat_conj mem hirr _ _ _).mpr
      constructor
      · obtain ⟨p, hpv, hp⟩ := hPower x hxv
        apply (sat_ex mem hirr _ c _).mpr
        refine ⟨p, (sat_conj mem hirr _ _ _).mpr ⟨?_, ?_⟩⟩
        · intro z hz
          have hzSub : PositiveClosure.Sub mem z x := by
            simpa [PositiveClosure.Sub, Tarski.Sat, update, hca, hcb, hab, Ne.symm hab,
              Ne.symm hca, Ne.symm hcb] using hz
          simpa [Tarski.Sat, update, hca, hcb, hab, Ne.symm hab,
            Ne.symm hca, Ne.symm hcb] using hp z hzSub
        · simpa [Tarski.Sat, update, hca, hcb, hab, Ne.symm hab,
            Ne.symm hca, Ne.symm hcb] using hpv
      · intro z hz
        have hzx : mem z x := by
          simpa [Tarski.Sat, update, hca, hcb, hab, Ne.symm hab,
            Ne.symm hca, Ne.symm hcb] using hz
        simpa [Tarski.Sat, update, hca, hcb, hab, Ne.symm hab,
          Ne.symm hca, Ne.symm hcb] using hTrans x hxv z hzx
  · simpa [Tarski.Sat, update, hcb] using hav

private theorem updates_commute (e : Nat → V) (a b : Nat) (hab : a ≠ b) (x y : V) :
    update (update e b y) a x = update (update e a x) b y := by
  funext n
  by_cases ha : n = a <;> by_cases hb : n = b <;>
    simp [update, ha, hb, hab, Ne.symm hab] at *

private theorem update_overwrite (e : Nat → V) (a : Nat) (x y : V) :
    update (update e a x) a y = update e a y := by
  funext n
  by_cases hn : n = a <;> simp [update, hn]

/-- Matrix truth ignores its own code label, with zero handled semantically. -/
theorem forward_matrix (mem : V → V → Prop) (a b c : Nat)
    (e : Nat → V) (v x y : V) :
    Tarski.Sat mem (update (update (update e c v) a x) b y) (Code254.dec c) ↔
      Tarski.Sat mem (update (update e a x) b y) (Code254.dec c) :=
  DecodeFresh254.sat_context_update_own_code mem c a b e v x y

theorem support_matrix (mem : V → V → Prop) (a b c : Nat) (hab : a ≠ b)
    (e : Nat → V) (v x y : V) :
    Tarski.Sat mem (update (update (update e c v) b y) a x) (Code254.dec c) ↔
      Tarski.Sat mem (update (update e a x) b y) (Code254.dec c) := by
  rw [updates_commute _ a b hab]
  exact forward_matrix mem a b c e v x y

/-- The colliding binders have a vacuous forward clause under raw IR. -/
theorem namedG_same (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hG : FullGIC mem) (a c : Nat) (hca : c ≠ a) (e : Nat → V) :
    Tarski.Sat mem e (namedG a a c (Code254.dec c)) := by
  obtain ⟨v, hs, _⟩ := (sat_gicForm mem .fBot e).mp (hG .fBot e) (e 0)
  have hEmpty : ∀ y, ¬ mem y v := by
    intro y hy
    obtain ⟨x, hx⟩ := hs y hy
    exact hx
  apply (sat_ex mem hirr e c _).mpr
  refine ⟨v, (sat_conj mem hirr _ _ _).mpr ⟨?_, ?_⟩⟩
  · intro x hx
    have hxx : mem x x := by simpa [Tarski.Sat, update] using hx
    exact (hirr x hxx).elim
  · intro y hy
    have hyv : mem y v := by simpa [Tarski.Sat, update, hca] using hy
    exact (hEmpty y hyv).elim

/-- The distinct-binder case uses exactly the native matrix's image instance. -/
theorem namedG_distinct (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hG : FullGIC mem) (a b c : Nat) (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (e : Nat → V) :
    Tarski.Sat mem e (namedG a b c (Code254.dec c)) := by
  obtain ⟨v, hs, hc⟩ := matrix_instance mem hG a b c e (e b)
  apply (sat_ex mem hirr e c _).mpr
  refine ⟨v, (sat_conj mem hirr _ _ _).mpr ⟨?_, ?_⟩⟩
  · intro x hx y hxy
    have hxb : mem x (e b) := by
      simpa [Tarski.Sat, update, hca, hcb, hab, Ne.symm hab,
        Ne.symm hca, Ne.symm hcb] using hx
    have hxy' := (forward_matrix mem a b c e v x y).mp hxy
    obtain ⟨z, hzv, hxz⟩ := hc x hxb ⟨y, hxy'⟩
    apply (sat_ex mem hirr _ b _).mpr
    refine ⟨z, (sat_conj mem hirr _ _ _).mpr ⟨?_, ?_⟩⟩
    · rw [update_overwrite]
      exact (forward_matrix mem a b c e v x z).mpr hxz
    · simpa [Tarski.Sat, update, hca, hcb, hab, Ne.symm hab,
        Ne.symm hca, Ne.symm hcb] using hzv
  · intro y hy
    have hyv : mem y v := by
      simpa [Tarski.Sat, update, hca, hcb, hab, Ne.symm hab,
        Ne.symm hca, Ne.symm hcb] using hy
    obtain ⟨x, hxy⟩ := hs y hyv
    apply (sat_ex mem hirr _ a _).mpr
    exact ⟨x, (support_matrix mem a b c hab e v x y).mpr hxy⟩

theorem namedG_of_fullGIC (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hG : FullGIC mem) (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b)
    (e : Nat → V) : Tarski.Sat mem e (namedG a b c (Code254.dec c)) := by
  by_cases hab : a = b
  · subst b
    exact namedG_same mem hirr hG a c hca e
  · exact namedG_distinct mem hirr hG a b c hab hca hcb e

/-- The original atomic gates, with no a!=b premise. -/
theorem named_vacuity (mem : V → V → Prop) (a b c : Nat)
    (hca : c ≠ a) (hcb : c ≠ b) (e : Nat → V) :
    Tarski.Sat mem e (.imp (.rel a b) (.all c (.rel a b))) ∧
      Tarski.Sat mem e (.imp (.eq a b) (.all c (.eq a b))) := by
  constructor <;> intro h x <;>
    simpa [Tarski.Sat, update, Ne.symm hca, Ne.symm hcb] using h

/-- Exact decoded-bundle model interface, with both original gates retained. -/
theorem modelsDecoded (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hC : Containers mem) (hG : FullGIC mem) : Code254Models.ModelsDecoded mem := by
  intro a b c hca hcb e
  apply (sat_dec_bundle_named mem hirr a b c e).mpr
  apply (sat_conj mem hirr _ _ _).mpr
  refine ⟨(sat_conj mem hirr _ _ _).mpr ⟨?_, ?_⟩,
    (sat_conj mem hirr _ _ _).mpr (named_vacuity mem a b c hca hcb e)⟩
  · exact namedC_of_containers mem hirr hC a b c hca hcb e
  · exact namedG_of_fullGIC mem hirr hG a b c hca hcb e

/-- The existing EncBundle adapter already supplies every native Form instance. -/
theorem fullGIC_of_encodable (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (h : Code254Models.ModelsEncodable mem) (valuation : Nat → V) : FullGIC mem := by
  intro phi env
  exact (sat_gicForm mem phi env).mpr
    (Code254GIC.collection_of_matrix mem hirr valuation h phi env)

/-- The opposite model comparison uses actual matrix adapters, not a quotient. -/
theorem decoded_of_encodable (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (h : Code254Models.ModelsEncodable mem) (valuation : Nat → V) :
    Code254Models.ModelsDecoded mem :=
  modelsDecoded mem hirr
    (Code254Containers.containers_of_encBundle mem hirr valuation h)
    (fullGIC_of_encodable mem hirr h valuation)

/-- Exact equality of the two theory-model obligations on an irreflexive
structure with a supplied valuation. This does not assert model existence. -/
theorem modelsDecoded_iff_modelsEncodable (mem : V → V → Prop)
    (hirr : ∀ x, ¬ mem x x) (valuation : Nat → V) :
    Code254Models.ModelsDecoded mem ↔ Code254Models.ModelsEncodable mem :=
  ⟨Code254Models.encodable_of_decoded mem hirr,
    fun h => decoded_of_encodable mem hirr h valuation⟩

/-- Soundness applies at an actual supplied valuation, excluding the empty-domain loophole. -/
theorem no_refutation (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hC : Containers mem) (hG : FullGIC mem) (valuation : Nat → V) :
    ¬ Code254.C254 Code254.F :=
  Code254Models.no_refutation_of_decoded mem hirr (modelsDecoded mem hirr hC hG) valuation

end SetTheory.BusyBeaver.ZFC.NativeDecoded254
