import OAI.Combinatorics.Progressions.Linear.DualIdealSteps

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualBCH_insertion_quotient (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) (z : DualGroup hnil) (e m : L)
    (hz : dualTangentLinear z.coord ∈ I) (he : e ∈ I) (hm : m ∈ I) :
    lieBCH s
      (lieBCH s
        (lieBCH s (-lieQuotientMap J e)
          (lieQuotientMap J (dualBaseLinear z.coord + dualTangentLinear z.coord)))
        (-lieQuotientMap J m))
      (-lieQuotientMap J (dualBaseLinear z.coord)) =
      lieQuotientMap J (dualLogDerivative z - e - dualAdjoint (dualBaseHom z) m) := by
  have ha : dualInfinitesimal (-e) ∈ dualIdealSubalgebra I := by
    rw [mem_dualIdealSubalgebra, dualTangentLinear_infinitesimal]
    exact I.neg_mem he
  have hb : z.coord ∈ dualIdealSubalgebra I := hz
  have hc : dualInfinitesimal (-m) ∈ dualIdealSubalgebra I := by
    rw [mem_dualIdealSubalgebra, dualTangentLinear_infinitesimal]
    exact I.neg_mem hm
  have hd : -dualConstantLie (dualBaseLinear z.coord) ∈ dualIdealSubalgebra I := by
    rw [mem_dualIdealSubalgebra, map_neg, dualTangentLinear_constant, neg_zero]
    exact I.zero_mem
  have hab := lieBCH_mem (dualIdealSubalgebra I) s ha hb
  have habc := lieBCH_mem (dualIdealSubalgebra I) s hab hc
  have h := congrArg (fun g : DualGroup hnil => dualQuotientEvaluate J g.coord)
    (dualBCH_insertion_identity z e m)
  change dualQuotientEvaluate J
    (lieBCH s (lieBCH s (lieBCH s (dualInfinitesimal (-e)) z.coord) (dualInfinitesimal (-m)))
      (-dualConstantLie (dualBaseLinear z.coord))) =
    dualQuotientEvaluate J (dualInfinitesimal (dualLogDerivative z - e - dualAdjoint (dualBaseHom z) m)) at h
  rw [dualQuotientEvaluate_lieBCH I J hIJ s habc hd,
    dualQuotientEvaluate_lieBCH I J hIJ s hab hc,
    dualQuotientEvaluate_lieBCH I J hIJ s ha hb] at h
  simpa only [dualQuotientEvaluate_apply, map_neg, dualBaseLinear_infinitesimal,
    dualTangentLinear_infinitesimal, dualBaseLinear_constant, dualTangentLinear_constant,
    zero_add, add_zero] using h

end Erdos3.NilpotentLieBCHGroup

end

end OAI
