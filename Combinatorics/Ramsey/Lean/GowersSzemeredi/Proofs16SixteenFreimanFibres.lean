import GowersSzemeredi.Proofs16ProgressionExactSixteenRelations
import Mathlib.Data.List.OfFn

/-! The native order-eight Freiman interface on each actual active fibre.
For a fixed Bohr argument y, only indices whose own local domains contain y
are used. No common-frequency or extension hypothesis is silently added. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

/-- Enumerate a multiset by its actual cardinality, retaining repetitions. -/
theorem multiset_fin_enumeration {X : Type*} {n : Nat} (s : Multiset X) (hs : s.card = n) :
    ∃ f : Fin n → X, (List.ofFn f : Multiset X) = s := by
  have hlen : s.toList.length = n := (Multiset.length_toList s).trans hs
  let f : Fin n → X := fun i => s.toList.get (Fin.cast hlen.symm i)
  have heq : List.ofFn f = s.toList :=
    (List.ofFn_congr hlen s.toList.get).symm.trans (List.ofFn_get s.toList)
  exact ⟨f, by rw [heq, Multiset.coe_toList]⟩

/-- Enumeration identifies the multiset sum with the finite indexed sum. -/
theorem multiset_ofFn_fin_sum {G : Type*} [AddCommMonoid G] {n : Nat} (f : Fin n → G) :
    (List.ofFn f : Multiset G).sum = ∑ i, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    change (List.ofFn f).sum = _
    rw [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ]
    exact congrArg (fun z => f 0 + z) (ih (fun i => f i.succ))

/-- Exact sixteen-endpoint identities are order-eight Freiman linearity
in the index variable, on each fibre's genuine local-map domain. -/
theorem freiman_eight_on_active_fibre_of_sixteen {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (rho : Real)
    (h16 : ∀ q : PairedSixteenTuple N, (∀ i, (q i).1 ∈ S ∧ (q i).2 ∈ S) →
      pairedSixteenIndex q = 0 → ∀ y ∈ bohr (pairedSixteenSpectrum T q) rho,
        pairedSixteenDefect L q y = 0) (y : ZMod N) :
    FreimanHom 8 (S.filter fun x => y ∈ bohr (T x) rho) (fun x => L x y) := by
  refine ⟨Set.mapsTo_univ _ _, ?_⟩
  intro s t hs ht hsc htc hsum
  obtain ⟨a, ha⟩ := multiset_fin_enumeration s hsc
  obtain ⟨b, hb⟩ := multiset_fin_enumeration t htc
  have hmemA : ∀ i, a i ∈ S ∧ y ∈ bohr (T (a i)) rho := by
    intro i
    have hm : a i ∈ s := by
      rw [← ha]
      exact Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩)
    exact Finset.mem_filter.mp (hs hm)
  have hmemB : ∀ i, b i ∈ S ∧ y ∈ bohr (T (b i)) rho := by
    intro i
    have hm : b i ∈ t := by
      rw [← hb]
      exact Multiset.mem_coe.mpr (List.mem_ofFn.mpr ⟨i,rfl⟩)
    exact Finset.mem_filter.mp (ht hm)
  let q : PairedSixteenTuple N := fun i => (a i,b i)
  have hindex : pairedSixteenIndex q = 0 := by
    rw [← ha, ← hb, multiset_ofFn_fin_sum, multiset_ofFn_fin_sum] at hsum
    change (∑ i : Fin 8, (a i-b i)) = 0
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hsum
  have hdom : y ∈ bohr (pairedSixteenSpectrum T q) rho :=
    (mem_paired_sixteen_spectrum_bohr T q rho y).mpr (fun i => ⟨(hmemA i).2,(hmemB i).2⟩)
  have hz := h16 q (fun i => ⟨(hmemA i).1,(hmemB i).1⟩) hindex y hdom
  change (∑ i : Fin 8, (L (a i) y-L (b i) y)) = 0 at hz
  rw [Finset.sum_sub_distrib] at hz
  rw [← ha, ← hb]
  simp only [Multiset.map_coe]
  exact sub_eq_zero.mp hz

end LeanProofs.GowersSzemeredi
