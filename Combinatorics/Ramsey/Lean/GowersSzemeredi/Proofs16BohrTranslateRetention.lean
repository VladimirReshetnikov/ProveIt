import GowersSzemeredi.Proofs16IndexedTranslateRetention

/-! Recenter a Freiman map while restricting indexed configurations to
a translated small test set inside its Bohr domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem bohr_freiman_translate_retention {N : Nat} [NeZero N] {I : Type*}
    (Q : Finset I) (x : I → ZMod N) (Gamma P : Finset (ZMod N))
    (psi : ZMod N → ZMod N) {rho eta mass : Real}
    (hrho : 0 ≤ rho) (heta : 0 < eta) (hmass : 0 < mass)
    (hQ : mass ≤ Q.card) (hP : eta*N ≤ (P.card : Real))
    (hx : ∀ q ∈ Q, x q ∈ bohr Gamma (rho/2))
    (hPsub : P ⊆ bohr Gamma (rho/2))
    (hpsi : FreimanHom 2 (bohr Gamma rho) psi) (hzero : psi 0 = 0) :
    ∃ (t : ZMod N) (R : Finset I), R ⊆ Q ∧ eta*mass ≤ (R.card : Real) ∧
      t ∈ bohr Gamma rho ∧
      ∀ q ∈ R, x q-t ∈ P ∧ psi (x q) = psi t+psi (x q-t) := by
  obtain ⟨t,ht⟩ := exists_dense_indexed_translate Q x P hmass.le hQ hP
  let R := Q.filter fun q => x q-t ∈ P
  have hRne : R.Nonempty := Finset.card_pos.mp (by
    have hpos : (0 : Real) < R.card := (mul_pos heta hmass).trans_le ht
    exact_mod_cast hpos)
  obtain ⟨q0,hq0⟩ := hRne
  obtain ⟨hq0Q,hq0P⟩ := Finset.mem_filter.mp hq0
  have htB : t ∈ bohr Gamma rho := by
    have h := bohr_add_half (hx q0 hq0Q) (neg_mem_bohr (hPsub hq0P))
    rwa [show x q0 + -(x q0-t) = t by ring] at h
  refine ⟨t,R,Finset.filter_subset _ _,ht,htB,?_⟩
  intro q hq
  obtain ⟨hqQ,hqP⟩ := Finset.mem_filter.mp hq
  have hxB : x q ∈ bohr Gamma rho := bohr_mono_radius Gamma (by linarith) (hx q hqQ)
  have hdB : x q-t ∈ bohr Gamma rho := bohr_mono_radius Gamma (by linarith) (hPsub hqP)
  have hlin := hpsi.add_eq_add hxB (zero_mem_bohr Gamma hrho) htB hdB (by ring)
  exact ⟨hqP,by simpa only [hzero,add_zero] using hlin⟩

end LeanProofs.GowersSzemeredi
