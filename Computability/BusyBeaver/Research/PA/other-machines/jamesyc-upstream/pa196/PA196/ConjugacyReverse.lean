module
public import PA196.Conjugacy
@[expose] public section
namespace PA196.Conjugacy
open M6.Zip

theorem halts_reflection {c : Conf} (hq : c.q < 197)
    (h : Halts Table.machine (mapConf c)) : Halts Literal.machine c := by
  obtain ⟨d,⟨n,hr⟩,hs⟩ := h
  rw [run_conjugate n c hq] at hr
  cases hc : run machine n c with
  | none => simp [hc] at hr
  | some e =>
    have he : mapConf e=d := by simpa [hc] using hr
    subst d
    refine ⟨e,⟨n,hc⟩,?_⟩
    rw [step_conjugate e (run_bounded hq hc)] at hs
    cases ht : step machine e with
    | none => rfl
    | some f => simp [ht] at hs

#print axioms halts_reflection
end PA196.Conjugacy
