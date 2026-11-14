import PA195AllTape
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA195LocalQuotient

def translate (k : Int) (c : Configuration) : Configuration :=
  ⟨c.state, c.pos + k, fun x => c.tape (x - k)⟩

theorem translate_update (t : Int → Bool) (p k : Int) (b : Bool) :
    (fun x => Function.update t p b (x - k)) =
      Function.update (fun x => t (x - k)) (p + k) b := by
  funext x
  simp only [Function.update_apply]
  have h : x - k = p ↔ x = p + k := by omega
  simp [h]

theorem fullStep_translate (rows : List Row) (c : Configuration) (k : Int) :
    fullStep rows (translate k c) = (fullStep rows c).map (translate k) := by
  cases hr : lookup rows c.state (c.tape c.pos) with
  | none => simp [fullStep, translate, hr]
  | some r =>
    have ht : (fun x => Function.update c.tape c.pos r.write (x - k)) =
        Function.update (fun x => c.tape (x - k)) (c.pos + k) r.write :=
      translate_update c.tape c.pos k r.write
    simp [fullStep, translate, hr, ← ht]
    omega

theorem fullRun_translate (rows : List Row) (n : Nat) (c : Configuration) (k : Int) :
    fullRun rows n (translate k c) = (fullRun rows n c).map (translate k) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [fullRun, fullStep_translate]
    cases hs : fullStep rows c with
    | none => simp
    | some c' => simp [ih]

/-- The 28 checked reader cases work at any head coordinate on any full tape. -/
theorem checked_case_any_head (c : Case) (hc : c ∈ cases) (k : Int) (t : Int → Bool)
    (hleft : t (k - 1) = c.left) (hhere : t k = c.read) :
    ∃ a : Configuration,
      fullStep parent ⟨c.state, k, t⟩ = some a ∧
      fullRun folded c.duration ⟨project c.state, k, t⟩ =
        some ⟨project a.state, a.pos, a.tape⟩ := by
  let shifted : Int → Bool := fun i => t (i + k)
  have hl : shifted (-1) = c.left := by
    dsimp [shifted]
    convert hleft using 1 <;> congr 1 <;> omega
  have hh : shifted 0 = c.read := by simpa [shifted] using hhere
  obtain ⟨a, ha, hb⟩ := checked_case_all_tapes c hc shifted hl hh
  have hstart (q : Nat) : translate k ⟨q, 0, shifted⟩ = ⟨q, k, t⟩ := by
    have he : (fun x => shifted (x - k)) = t := by
      funext x
      dsimp [shifted]
      congr 1
      omega
    simp [translate, he]
  refine ⟨translate k a, ?_, ?_⟩
  · have h := fullStep_translate parent ⟨c.state, 0, shifted⟩ k
    rw [hstart, ha] at h
    exact h
  · have h := fullRun_translate folded c.duration ⟨project c.state, 0, shifted⟩ k
    rw [hstart, hb] at h
    exact h

#print axioms checked_case_any_head
#print axioms fullRun_translate
end PA195LocalQuotient
