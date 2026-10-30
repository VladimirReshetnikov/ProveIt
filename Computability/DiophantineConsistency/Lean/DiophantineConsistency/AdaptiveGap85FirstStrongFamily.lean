import DiophantineConsistency.AdaptiveGap85FirstStrongBinding
import DiophantineConsistency.AdaptiveGap85StrongSeed

/-! First+strong actual-factor witnesses for arbitrary positive natural ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85FirstStrongFamily
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveGap85Factors AdaptiveGap85WeakFamily AdaptiveGap85FirstStrongBinding AdaptiveGap85FamilyBinding
open AdaptiveGap85StrongSeed

/-- For positive natural first and second ports, there are positive integer
witnesses violating the reverse bound whose actual first and strong factors
are one. No main or auxiliary factor unit or full zero is asserted. -/
theorem first_strong_weak_counterexample (b k : ℕ) (hb : 0<b) (hk : 0<k) (mu nu : ℤ) :
    ∃ w : Fin 13 → ℤ, (∀i,0<w i) ∧
      ¬(w 1+w 2<1+w 0*(b:ℤ)) ∧
      ((factors (ports (b:ℤ) (k:ℤ) mu nu)).1).eval w=1 ∧
      ((factors (ports (b:ℤ) (k:ℤ) mu nu)).2.2.2).eval w=1 := by
  let a : ℕ := 2*(b+1)^3
  obtain ⟨f,i,hf,hi,hs⟩ := strong_seed_at_successor (V:=ℕ) a
  have hc : a+1=1+2*(b+1)^3 := by dsimp [a]; omega
  have hd : ArithmeticPellRecurrence.delta a=(2*(b+1)^3+1)*(2*(b+1)^3+3) := by
    simp [ArithmeticPellRecurrence.delta,a]
  rw [hc,hd] at hs
  have hstrong : let Y : ℤ := ((b:ℤ)+1)^3
      let c := 1+2*Y
      let Delta := (2*Y+1)*(2*Y+3)
      (c*c*(i:ℤ))*(c*c*(i:ℤ))+Delta=Delta*((f:ℤ)*(f:ℤ)) := by
    dsimp
    exact_mod_cast hs
  have hdec : (k:ℤ)=(b:ℤ)*((k/b:ℕ):ℤ)+((k%b:ℕ):ℤ) := by
    exact_mod_cast (Nat.div_add_mod k b).symm
  have hbeta : (1:ℤ)≤b := by exact_mod_cast hb
  have hK : (1:ℤ)≤k := by exact_mod_cast hk
  have hgen := actual_family_properties (b:ℤ) (k:ℤ) mu nu hbeta hK
  dsimp at hgen
  let w := witnessStrong (b:ℤ) (k:ℤ) ((k%b:ℕ):ℤ) ((k/b:ℕ):ℤ) (f:ℤ) (i:ℤ)
  have hw : ∀j,0<w j := by
    intro j
    by_cases h3 : j=3
    · subst j
      simpa [w,witnessStrong] using (show (0:ℤ)<f by exact_mod_cast hf)
    by_cases h4 : j=4
    · subst j
      simpa [w,witnessStrong] using (show (0:ℤ)<i by exact_mod_cast hi)
    · have he : w j = witness (b:ℤ) (k:ℤ) ((k:ℤ)%(b:ℤ)) ((k:ℤ)/(b:ℤ)) j := by
        fin_cases j
        all_goals first | contradiction | rfl
      rw [he]
      exact hgen.1 j
  have hnot : ¬(w 1+w 2<1+w 0*(b:ℤ)) := by
    simpa [w,witnessStrong,witness,Int.natCast_emod,Int.natCast_ediv] using hgen.2.1
  have hfac := first_and_strong_actual (b:ℤ) (k:ℤ) ((k%b:ℕ):ℤ) ((k/b:ℕ):ℤ) (f:ℤ) (i:ℤ) mu nu hdec hstrong
  exact ⟨w,hw,hnot,hfac.1,hfac.2⟩
end DiophantineConsistency.AdaptiveGap85FirstStrongFamily
