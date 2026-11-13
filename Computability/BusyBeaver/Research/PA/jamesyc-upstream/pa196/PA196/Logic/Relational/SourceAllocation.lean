module
public import PA196.Logic.Relational.Freshening
public import M6PA.Calibration.RelationalSourceRewriting
@[expose] public section

namespace PA196.Logic.Relational.Source
open FFL FFL.FirstOrder
open M6.PA.RelationalSource
open M6.PA.NativeCalculus (renameLabel)
open PA196.Logic PA196.Logic.Relational

theorem toNamed_binders_below {ξ : Type} {n : Nat} (p : Semiformula language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (lo v : Nat) (hv : v < lo) :
    (toNamed p b f lo).binders v = false := by
  induction p generalizing lo with
  | verum | falsum => rfl
  | rel r ts | nrel r ts => cases r <;> rfl
  | and p q ihp ihq | or p q ihp ihq =>
    simp [toNamed,M6.PA.NativeCalculus.Named.binders,ihp b lo hv,ihq b lo hv]
  | all p ih | exs p ih =>
    simp [toNamed,M6.PA.NativeCalculus.Named.binders,Nat.ne_of_lt hv,
      ih (Fin.cases lo b) (lo+1) (by omega)]

theorem toNamed_freshen {ξ : Type} {n : Nat} (p : Semiformula language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (lo k : Nat) (hlo : 0 < lo)
    (hb : ∀ i,b i < lo) (hf : ∀ i,f i < lo) (hk : lo < k) :
    (toNamed p b f lo).freshen k = toNamed p b f k := by
  induction p generalizing lo k with
  | verum | falsum => rfl
  | rel r ts | nrel r ts => cases r <;> rfl
  | and p q ihp ihq | or p q ihp ihq =>
    simp only [toNamed,M6.PA.NativeCalculus.Named.freshen,ihp b lo k hlo hb hf hk,ihq b lo k hlo hb hf hk]
  | all p ih | exs p ih =>
    have hb' : ∀ i,(Fin.cases (motive := fun _ => Nat) lo b) i < lo+1 := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simpa using Nat.lt_trans (hb j) (Nat.lt_succ_self lo)
    have hf' : ∀ i,f i < lo+1 := fun i => Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
    have hbRename : renameLabel lo k ∘ Fin.cases lo b = Fin.cases k b := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [renameLabel]
      · simp [renameLabel,Nat.ne_of_lt (hb j)]
    have hfRename : renameLabel lo k ∘ f = f := by
      funext i
      simp [renameLabel,Nat.ne_of_lt (hf i)]
    simp only [toNamed,M6.PA.NativeCalculus.Named.freshen,M6.PA.NativeCalculus.Named.replace,
      ih (Fin.cases lo b) (lo+1) (k+1) (by omega) hb' hf' (by omega),
      toNamed_replace p (Fin.cases lo b) f (k+1) lo k (by omega) (Nat.ne_of_gt hlo),
      hbRename,hfRename]

def reallocation {ξ : Type} {n : Nat} (p : Semiformula language ξ n)
    (b : Fin n → Nat) (f : ξ → Nat) (lo lo' z : Nat)
    (hlo : 0 < lo) (hlo' : 0 < lo')
    (hb : ∀ i,b i < min lo lo') (hf : ∀ i,f i < min lo lo')
    (hz : max (lo + depth p) (lo' + depth p) ≤ z) :
    Proof (wim (relationalCode z (toNamed p b f lo)) (relationalCode z (toNamed p b f lo'))) ×
    Proof (wim (relationalCode z (toNamed p b f lo')) (relationalCode z (toNamed p b f lo))) := by
  let k := lo+lo'+depth p+z+1
  have hb1 : ∀ i,b i < lo := fun i => Nat.lt_of_lt_of_le (hb i) (Nat.min_le_left _ _)
  have hb2 : ∀ i,b i < lo' := fun i => Nat.lt_of_lt_of_le (hb i) (Nat.min_le_right _ _)
  have hf1 : ∀ i,f i < lo := fun i => Nat.lt_of_lt_of_le (hf i) (Nat.min_le_left _ _)
  have hf2 : ∀ i,f i < lo' := fun i => Nat.lt_of_lt_of_le (hf i) (Nat.min_le_right _ _)
  have hz1 := toNamed_reserved p b f lo z hlo hb1 hf1 (by omega)
  have hz2 := toNamed_reserved p b f lo' z hlo' hb2 hf2 (by omega)
  have hn1 : ∀ v,(toNamed p b f lo).names v = true → v < k := by
    intro v hv
    have h := toNamed_names_lt p b f lo v hlo hb1 hf1 hv
    dsimp [k]; omega
  have hn2 : ∀ v,(toNamed p b f lo').names v = true → v < k := by
    intro v hv
    have h := toNamed_names_lt p b f lo' v hlo' hb2 hf2 hv
    dsimp [k]; omega
  let hp := relationalFreshening (toNamed p b f lo) z k hz1 (by dsimp [k]; omega) hn1
  let hq := relationalFreshening (toNamed p b f lo') z k hz2 (by dsimp [k]; omega) hn2
  have he1 := toNamed_freshen p b f lo k hlo hb1 hf1 (by dsimp [k]; omega)
  have he2 := toNamed_freshen p b f lo' k hlo' hb2 hf2 (by dsimp [k]; omega)
  rw [he1] at hp
  rw [he2] at hq
  exact ⟨implicationCompose hp.1 hq.2,implicationCompose hq.1 hp.2⟩

#print axioms toNamed_freshen
#print axioms reallocation
end PA196.Logic.Relational.Source

