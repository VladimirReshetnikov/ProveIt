import PA194RelationalSourceInstantiation

namespace PA194Logic.Relational.Source
open LO LO.FirstOrder
open M6.PA.RelationalSource
open M6.PA.NativeCalculus (renameLabel)
open PA194Logic PA194Logic.Relational

theorem termLabel_ne {ξ : Type} {n : Nat} (t : Semiterm language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (v : Nat)
    (hb : ∀ i,b i ≠ v) (hf : ∀ i,f i ≠ v) : termLabel t b f ≠ v := by
  cases t with
  | bvar i => exact hb i
  | fvar i => exact hf i
  | func fn _ => nomatch fn

theorem atomNamed_avoids {ξ : Type} {n k : Nat} (r : Relation k)
    (ts : Fin k → Semiterm language ξ n) (b : Fin n → Nat) (f : ξ → Nat) (v : Nat)
    (hb : ∀ i,b i ≠ v) (hf : ∀ i,f i ≠ v) : (atomNamed r ts b f).names v = false := by
  cases r <;> simp [atomNamed,M6.PA.NativeCalculus.Named.names,Ne.symm (termLabel_ne _ b f v hb hf)]

theorem toNamed_avoids {ξ : Type} {n : Nat} (p : Semiformula language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (lo v : Nat) (hv : 0 < v) (hlo : v < lo)
    (hb : ∀ i,b i ≠ v) (hf : ∀ i,f i ≠ v) : (toNamed p b f lo).names v = false := by
  induction p generalizing lo with
  | verum => rfl
  | falsum => simp [toNamed,M6.PA.NativeCalculus.Named.names,Nat.ne_of_gt hv]
  | rel r ts | nrel r ts => exact atomNamed_avoids r ts b f v hb hf
  | and p q ihp ihq | or p q ihp ihq =>
    simp only [toNamed,M6.PA.NativeCalculus.Named.names,ihp b lo hlo hb,ihq b lo hlo hb,Bool.false_or]
  | all p ih | exs p ih =>
    have hb' : ∀ i,(Fin.cases (motive := fun _ => Nat) lo b) i ≠ v := by
      intro i
      refine Fin.cases ?_ (fun j => hb j) i
      exact Nat.ne_of_gt hlo
    simp only [toNamed,M6.PA.NativeCalculus.Named.names,ih (Fin.cases lo b) (lo+1) (by omega) hb',
      beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hlo),Bool.false_or]

def sourceVacuity {ξ : Type} {n : Nat} (p : Semiformula language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (lo v z : Nat) (hv : 0 < v) (hlo : v < lo)
    (hb : ∀ i,b i ≠ v) (hf : ∀ i,f i ≠ v) (hvz : v ≠ z) :
    Proof (wim (relationalCode z (toNamed p b f lo))
      (wal v (relationalCode z (toNamed p b f lo)))) := by
  have hn := toNamed_avoids p b f lo v hv hlo hb hf
  apply relationalCodeVacuity _ z v hvz
  · cases h : (toNamed p b f lo).free v
    · rfl
    · have := M6.PA.NativeCalculus.Named.free_in_names _ _ h; simp [hn] at this
  · cases h : (toNamed p b f lo).binders v
    · rfl
    · have := M6.PA.NativeCalculus.Named.binders_in_names _ _ h; simp [hn] at this

/-- The finite source context consists of negated sequent formulas. -/
def negativeContext {ξ : Type} {n : Nat} (ps : List (Semiformula language ξ n))
    (b : Fin n → Nat) (f : ξ → Nat) (lo z : Nat) : List Nat :=
  ps.map (fun p => wn (relationalCode z (toNamed p b f lo)))

def negativeContextVacuity {ξ : Type} {n : Nat}
    (ps : List (Semiformula language ξ n)) (b : Fin n → Nat) (f : ξ → Nat)
    (lo v z : Nat) (hv : 0 < v) (hlo : v < lo)
    (hb : ∀ i,b i ≠ v) (hf : ∀ i,f i ≠ v) (hvz : v ≠ z)
    (a : Nat) (ha : a ∈ negativeContext ps b f lo z) : Proof (wim a (wal v a)) := by
  cases ps with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons p ps =>
    by_cases h : a = wn (relationalCode z (toNamed p b f lo))
    · subst a
      exact negationVacuity v _ (sourceVacuity p b f lo v z hv hlo hb hf hvz)
    · exact negativeContextVacuity ps b f lo v z hv hlo hb hf hvz a
        ((List.mem_cons.mp ha).resolve_left h)

def generalizeNegativeContext {ξ : Type} {n a : Nat}
    (ps : List (Semiformula language ξ n)) (b : Fin n → Nat) (f : ξ → Nat)
    (lo v z : Nat) (hv : 0 < v) (hlo : v < lo)
    (hb : ∀ i,b i ≠ v) (hf : ∀ i,f i ≠ v) (hvz : v ≠ z)
    (d : Context (negativeContext ps b f lo z) a) :
    Context (negativeContext ps b f lo z) (wal v a) :=
  d.generalize v (negativeContextVacuity ps b f lo v z hv hlo hb hf hvz)

#print axioms toNamed_avoids
#print axioms generalizeNegativeContext
end PA194Logic.Relational.Source

