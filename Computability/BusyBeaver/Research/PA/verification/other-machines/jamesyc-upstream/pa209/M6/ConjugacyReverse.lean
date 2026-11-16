module
public import M6.Conjugacy
@[expose] public section
namespace M6.Conjugacy
open M6.Zip
/-- Reverse halting transport uses deterministic run conjugacy, not an
assumption that sparse auxiliary states are absent from arbitrary inputs. -/
theorem halts_reflection {c : Conf} (hq : c.q < 216)
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
end M6.Conjugacy
