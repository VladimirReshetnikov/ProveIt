import LeastPrefix

namespace BudgetAnalysis.Prefix
open BitIntegral (T Oracle)

abbrev Row := Sparse × Int

def rows : T → Sparse → List Row
  | .ret z, h => [(h,z)]
  | .ask q next, h =>
    match lookup h q with
    | some b => rows (next b) h
    | none => rows (next false) ((q,false)::h) ++ rows (next true) ((q,true)::h)

theorem extends_push (x : Oracle) (h : Sparse) (q : Nat) (b : Bool)
    (fresh : lookup h q = none) :
    Extends x (lookup ((q,b)::h)) ↔ Extends x (lookup h) ∧ x q = b := by
  constructor
  · intro hx
    refine ⟨?_, hx q b (by simp [lookup])⟩
    intro i c hi
    by_cases e : i = q
    · subst i
      simp [fresh] at hi
    · exact hx i c (by simp [lookup, e, hi])
  · rintro ⟨ext, forced⟩ i c hc
    by_cases e : i = q
    · subst i
      simpa [lookup] using forced.trans (by simpa [lookup] using hc : b = c)
    · exact ext i c (by simpa [lookup, e] using hc)

theorem rows_sound (t : T) (h : Sparse) (z : Row) (hz : z ∈ rows t h) (x : Oracle)
    (ext : Extends x (lookup z.1)) :
    Extends x (lookup h) ∧ Dialogue.eval x t = z.2 := by
  induction t generalizing h with
  | ret r =>
    simp only [rows, List.mem_singleton] at hz
    subst z
    exact ⟨ext, rfl⟩
  | ask q next ih =>
    cases key : lookup h q with
    | some b =>
      simp only [rows, key] at hz
      obtain ⟨eh, ev⟩ := ih b h hz
      have val := eh q b key
      exact ⟨eh, by simpa [Dialogue.eval, val] using ev⟩
    | none =>
      simp only [rows, key, List.mem_append] at hz
      have branch (b : Bool) (hz' : z ∈ rows (next b) ((q,b)::h)) :
          Extends x (lookup h) ∧ Dialogue.eval x (.ask q next) = z.2 := by
        obtain ⟨eh, ev⟩ := ih b _ hz'
        obtain ⟨base, val⟩ := (extends_push x h q b key).mp eh
        exact ⟨base, by simpa [Dialogue.eval, val] using ev⟩
      exact hz.elim (branch false) (branch true)

theorem rows_cover (t : T) (h : Sparse) (x : Oracle) (eh : Extends x (lookup h)) :
    ∃ z ∈ rows t h, Extends x (lookup z.1) ∧ Dialogue.eval x t = z.2 := by
  induction t generalizing h with
  | ret r => exact ⟨(h,r), by simp [rows], eh, rfl⟩
  | ask q next ih =>
    cases key : lookup h q with
    | some b =>
      have val := eh q b key
      simpa only [rows, key, Dialogue.eval, val] using ih b h eh
    | none =>
      have withBit := (extends_push x h q (x q) key).mpr ⟨eh,rfl⟩
      obtain ⟨z, mem, ext, val⟩ := ih (x q) _ withBit
      refine ⟨z, ?_, ext, val⟩
      simp only [rows, key, List.mem_append]
      cases b : x q <;> simp [b] at mem <;> simp [mem]

def forbidden (rs : List Row) (a : Nat) : List (Sparse × Sparse) :=
  (rs.flatMap (fun s => rs.map (fun t => (s,t)))).filterMap (fun (s,t) =>
    if a < (s.2 - t.2).natAbs then some (s.1,t.1) else none)

theorem forbidden_spec (rs : List Row) (a : Nat) (z : Sparse × Sparse) :
    z ∈ forbidden rs a ↔ ∃ s ∈ rs, ∃ t ∈ rs,
      a < (s.2 - t.2).natAbs ∧ z = (s.1,t.1) := by
  simp only [forbidden, List.mem_filterMap, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨s,t⟩, ⟨s',hs,t',ht,he⟩, hz⟩
    cases he
    split at hz
    · rename_i large
      exact ⟨s, hs, t, ht, large, (Option.some.inj hz).symm⟩
    · contradiction
  · rintro ⟨s,hs,t,ht,large,rfl⟩
    exact ⟨(s,t), ⟨s,hs,t,ht,rfl⟩, by simp [large]⟩

/-- The executable threshold computes exactly the prefix lengths controlling
    the oscillation of the returned integer labels at the specified tolerance. -/
theorem least_oscillation (t : T) (a n : Nat) :
    FitsAt (least (forbidden (rows t []) a)) n ↔
    ∀ x y, AgreeTo n x y → (Dialogue.eval x t - Dialogue.eval y t).natAbs ≤ a := by
  rw [least_spec, safePrefix_spec]
  have empty (x : Oracle) : Extends x (lookup []) := by
    intro i b hi
    contradiction
  constructor
  · intro safe x y same
    obtain ⟨s,hs,ex,sx⟩ := rows_cover t [] x (empty x)
    obtain ⟨r,hr,ey,ry⟩ := rows_cover t [] y (empty y)
    rw [sx, ry]
    apply Nat.le_of_not_gt
    intro large
    have forbiddenPair := (forbidden_spec _ a (s.1,r.1)).mpr ⟨s,hs,r,hr,large,rfl⟩
    exact safe _ forbiddenPair ⟨x,y,ex,ey,same⟩
  · rintro good z hz ⟨x,y,ex,ey,same⟩
    obtain ⟨s,hs,r,hr,large,rfl⟩ := (forbidden_spec ..).mp hz
    have sx := (rows_sound t [] s hs x ex).2
    have ry := (rows_sound t [] r hr y ey).2
    have small := good x y same
    rw [sx,ry] at small
    omega

/-- Crude all-branches upper bound used only for the existence proof. -/
def use : T → Nat
  | .ret _ => 0
  | .ask q next => max (q+1) (max (use (next false)) (use (next true)))

theorem eval_of_prefix (t : T) (n : Nat) (hn : use t ≤ n)
    (x y : Oracle) (same : AgreeTo n x y) : Dialogue.eval x t = Dialogue.eval y t := by
  induction t with
  | ret => rfl
  | ask q next ih =>
    simp only [use, Nat.max_le] at hn
    have eqBit := same q hn.1
    simp only [Dialogue.eval, ← eqBit]
    cases eq : x q with
    | false => exact ih false hn.2.1
    | true => exact ih true hn.2.2

theorem exists_least_oscillation (t : T) (a : Nat) :
    ∃ k, least (forbidden (rows t []) a) = some k ∧ ∀ n, k ≤ n ↔
      ∀ x y, AgreeTo n x y → (Dialogue.eval x t - Dialogue.eval y t).natAbs ≤ a := by
  have crude : FitsAt (least (forbidden (rows t []) a)) (use t) := by
    apply (least_oscillation t a (use t)).mpr
    intro x y same
    simp [eval_of_prefix t _ (Nat.le_refl _) x y same]
  cases value : least (forbidden (rows t []) a) with
  | none => simp [value, FitsAt] at crude
  | some k =>
    refine ⟨k, rfl, fun n => ?_⟩
    simpa only [value, FitsAt] using least_oscillation t a n

end BudgetAnalysis.Prefix
