import GowersSzemeredi.Proofs13IntegerEqualCover

/-! A common-step modular square has a genuine integer square of any
prescribed positive length below the explicit retained width. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem dense_common_step_integer_square {N : Nat} [NeZero N]
    (P R : ModAP N) (hP : P.IsProper) (hR : R.IsProper)
    (hlen : P.length = R.length) (hstep : P.step = R.step) (hm : 4 ≤ P.length)
    (B : Finset (Pair N)) (delta : Real) (hd : 0 < delta)
    (hB : B ⊆ P.carrier.product R.carrier)
    (hmass : delta * P.length * R.length ≤ B.card)
    (m : Nat) (hmpos : 0 < m) (hfit : (m : Real) ≤ delta * Real.sqrt P.length / 16) :
    ∃ Q T : NatAP, ∃ E : Finset (Pair N),
      Q.IsProper ∧ T.IsProper ∧ Q.step = T.step ∧ Q.length = m ∧ T.length = m ∧
      Q.carrier ⊆ Finset.range N ∧ T.carrier ⊆ Finset.range N ∧
      (Q.toModAP N).carrier ⊆ P.carrier ∧ (T.toModAP N).carrier ⊆ R.carrier ∧
      E ⊆ B ∧ E ⊆ (Q.toModAP N).carrier.product (T.toModAP N).carrier ∧
      delta / 16 * m * m ≤ E.card := by
  classical
  obtain ⟨U, V, D, hU, hV, hUV, hUN, hVN, hUP, hVR, hUlen, hVlen, hDB, hD, hmassD⟩ :=
    dense_common_step_integer_rectangle P R hP hR hlen hstep hm B delta hd hB hmass
  have hmU : m ≤ U.length := by exact_mod_cast hfit.trans hUlen
  have hmV : m ≤ V.length := by exact_mod_cast hfit.trans hVlen
  obtain ⟨Q, T, E, hQ, hT, hQT, hQlen, hTlen, hQU, hTV, hED, hE, hmassE⟩ :=
    dense_equal_integer_square U V hU hV hUV hUN hVN D (delta / 4)
      (by positivity) m hmpos hmU hmV hD hmassD
  have hQP : (Q.toModAP N).carrier ⊆ P.carrier := by
    rw [NatAP.toModAP_carrier] at hUP ⊢
    exact (Finset.image_mono _ hQU).trans hUP
  have hTR : (T.toModAP N).carrier ⊆ R.carrier := by
    rw [NatAP.toModAP_carrier] at hVR ⊢
    exact (Finset.image_mono _ hTV).trans hVR
  refine ⟨Q, T, E, hQ, hT, hQT, hQlen, hTlen, hQU.trans hUN, hTV.trans hVN,
    hQP, hTR, hED.trans hDB, hE, ?_⟩
  convert hmassE using 1; ring

end LeanProofs.GowersSzemeredi
