import GowersSzemeredi.Proofs16OffsetCollisionDensity
import GowersSzemeredi.Proofs16PopularFibreRetention

/-! Extract one Freiman coordinate from a dense indexed offset equation
while retaining a controlled portion of the original configurations. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def offsetFreimanRetention (delta : Real) : Real :=
  delta/2*((2 : Real)^(-(1882 : Real))*(((delta/2)^2)^4)^1164)

theorem offsetFreimanRetention_pos {delta : Real} (hd : 0 < delta) :
    0 < offsetFreimanRetention delta := by unfold offsetFreimanRetention; positivity

theorem offset_equation_retain_freiman_piece {N : Nat} [NeZero N] [Fact N.Prime] {I : Type*}
    [Fintype I] [DecidableEq I] (Q : Finset (I × ZMod N)) (a v : I → ZMod N)
    (f g : ZMod N → ZMod N) (M : Nat)
    (hM : 0 < M) (ha : ∀ z, (Finset.univ.filter fun i => a i = z).card ≤ M)
    (hval : ∀ p ∈ Q, f (p.2+a p.1)-g p.2 = v p.1)
    {delta : Real} (hd : 0 < delta) (hQ : delta*M*(N : Real)^2 ≤ Q.card) :
    ∃ (E : Finset (ZMod N)) (R : Finset (I × ZMod N)),
      E ⊆ Q.image (fun p => p.2+a p.1) ∧ R ⊆ Q ∧
      (∀ p ∈ R, p.2+a p.1 ∈ E) ∧ FreimanHom 8 E f ∧
      (2 : Real)^(-(1882 : Real))*(((delta/2)^2)^4)^1164*N ≤ E.card ∧
      offsetFreimanRetention delta*M*(N : Real)^2 ≤ R.card := by
  let endpoint (p : I × ZMod N) := p.2+a p.1
  let tau := delta*M*(N : Real)/2
  let P := popularEndpointFibres Q endpoint tau
  let Q' := Q.filter fun p => endpoint p ∈ P
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hm : (0 : Real) < M := by exact_mod_cast hM
  have htau : 0 < tau := by dsimp [tau]; positivity
  have hmass := popular_fibre_retained_mass Q endpoint htau.le
  have hQ' : (delta/2)*M*(N : Real)^2 ≤ Q'.card := by
    simp only [ZMod.card] at hmass
    change (Q.card : Real)-(N : Real)*tau ≤ (Q'.card : Real) at hmass
    dsimp [tau] at hmass
    nlinarith only [hmass,hQ]
  obtain ⟨E,hEP,hE,hF⟩ := offset_equation_freiman_piece Q' a v P f g M hM ha
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (fun p hp => hval p (Finset.mem_filter.mp hp).1) (by positivity) hQ'
  let R := Q.filter fun p => endpoint p ∈ E
  have hR : tau*E.card ≤ (R.card : Real) :=
    fibre_filter_mass_lower Q endpoint E (fun x hx => (Finset.mem_filter.mp (hEP hx)).2)
  refine ⟨E,R,fun x hx => popular_endpoint_mem_image Q endpoint htau (hEP hx),
    Finset.filter_subset _ _,fun p hp => (Finset.mem_filter.mp hp).2,hF,hE,?_⟩
  calc offsetFreimanRetention delta*M*(N : Real)^2 =
      tau*((2 : Real)^(-(1882 : Real))*(((delta/2)^2)^4)^1164*N) := by
        dsimp [offsetFreimanRetention,tau]
        ring
    _ ≤ tau*E.card := mul_le_mul_of_nonneg_left hE htau.le
    _ ≤ R.card := hR

end LeanProofs.GowersSzemeredi
