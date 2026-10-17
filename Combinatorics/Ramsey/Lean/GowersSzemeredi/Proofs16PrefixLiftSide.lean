import GowersSzemeredi.Proofs16PrefixLift
import GowersSzemeredi.Proofs16GlobalGraphCover
import GowersSzemeredi.Proofs16UnusedCoordinateLift

/-! Declarations of `Proofs16PrefixLift` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Any number of unused final coordinates can be added with the same
parameters. The graph-count reserve is required only in the final dimension. -/
theorem MultiplyLinearFunction.lift_prefix {N l d : Nat} [NeZero N] [Fact N.Prime]
    {gamma s : Real} {B : Finset (Point N l)} {phi : Point N l → ZMod N}
    (hML : MultiplyLinearFunction gamma s B phi)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 2 ≤ s)
    (hgraphs : ((3 ^ d : Nat) : Real) ≤ s) (hld : l ≤ d) :
    MultiplyLinearFunction gamma s (prefixDomain hld B)
      (fun z => phi (coordinatePrefix hld z)) := by
  by_cases hl : l = 0
  · subst l
    have heq : (fun z : Point N d => phi (coordinatePrefix hld z)) =
        (fun _ => phi (fun i => Fin.elim0 i)) := by
      funext z
      congr 1
      exact Subsingleton.elim _ _
    rw [heq]
    exact (isMultilinear_constant _).multiplyLinearFunction _ hg hg1 (by linarith)
  · induction d with
    | zero => omega
    | succ d ih =>
      by_cases heq : l = d + 1
      · subst l
        have hB : prefixDomain hld B = B := by
          ext z
          simp
        simpa only [hB, coordinatePrefix_self] using hML
      · have hld' : l ≤ d := by omega
        have hgprev : ((3 ^ d : Nat) : Real) ≤ s := by
          apply le_trans _ hgraphs
          exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (3 : Nat)) (Nat.le_succ d))
        have hp := (ih hgprev hld').lift_last hg hg1 hs hgraphs (by omega)
        have hdom : lastProductSet (prefixDomain hld' B) Finset.univ = prefixDomain hld B := by
          ext z
          simp only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and,
            and_true, mem_prefixDomain]
          rfl
        rw [hdom] at hp
        exact hp

end LeanProofs.GowersSzemeredi
