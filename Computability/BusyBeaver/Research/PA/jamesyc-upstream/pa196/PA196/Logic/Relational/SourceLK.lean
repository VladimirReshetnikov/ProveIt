module
public import PA196.Logic.Relational.SourceExistential
public import PA196.Logic.Relational.SourceGeneralization
public import M6PA.Calibration.RelationalSourceLK
public import PA196.Logic.Relational.SourceCode
@[expose] public section

namespace PA196.Logic.Relational.Source
open FFL FFL.FirstOrder
open M6.PA.RelationalSource
open M6.PA.NativeCalculus (renameLabel)
open PA196.Logic PA196.Logic.Relational

/-- A constructive finite-context sequent interpretation. -/
def Refutes (Γ : LK.Sequent language) (f : Nat → Nat) (lo z : Nat) : Type :=
  {C : List Nat} → (∀ p, p ∈ Γ → Context C (wn (code p f lo z))) → Context C 1

def Refutes.positive {Γ : LK.Sequent language} {p : Proposition language}
    {f : Nat → Nat} {lo z : Nat} (d : Refutes (Γ + ⦃p⦄) f lo z)
    {C : List Nat} (h : ∀ q,q ∈ Γ → Context C (wn (code q f lo z))) :
    Context C (code p f lo z) := by
  let hn := code p f lo z
  have r : Context (wn hn :: C) 1 := d fun q hq => by
    by_cases e : q = p
    · subst q
      exact .assumption (by simp [hn])
    · exact (h q ((Multiset.mem_add.mp hq).resolve_right (by simpa using e))).up (wn hn)
  exact r.deduction.dne

def refutesIdentity {k : Nat} (r : language.Rel k)
    (ts : Fin k → Semiterm language Nat 0) (f : Nat → Nat) (lo z : Nat) :
    Refutes ⦃Semiformula.rel r ts,Semiformula.nrel r ts⦄ f lo z := by
  intro C h
  exact Context.mp (h (.rel r ts) (by simp)) (h (.nrel r ts) (by simp))

def refutesVerum (f : Nat → Nat) (lo z : Nat) :
    Refutes (⦃Semiformula.verum⦄ : LK.Sequent language) f lo z := by
  intro C h
  exact Context.mp (.closed truthProof) (h .verum (by simp))

def refutesCut {Γ Δ : LK.Sequent language} {p : Proposition language}
    {f : Nat → Nat} {lo z : Nat}
    (d : Refutes (Γ + ⦃p⦄) f lo z)
    (e : Refutes (Δ + ⦃Semiformula.neg p⦄) f lo z) :
    Refutes (Γ + Δ) f lo z := by
  intro C h
  let hp := d.positive (fun q hq => h q (Multiset.mem_add.mpr (Or.inl hq)))
  let hn := e.positive (fun q hq => h q (Multiset.mem_add.mpr (Or.inr hq)))
  exact Context.mp hp (.mp hn (.closed (negationProof p Fin.elim0 f lo z).1))

def refutesWeakening {Γ : LK.Sequent language} {p : Proposition language}
    {f : Nat → Nat} {lo z : Nat} (d : Refutes Γ f lo z) :
    Refutes (Γ + ⦃p⦄) f lo z :=
  by
    intro C h
    exact d (fun q hq => h q (Multiset.mem_add.mpr (Or.inl hq)))

def refutesContraction {Γ : LK.Sequent language} {p : Proposition language}
    {f : Nat → Nat} {lo z : Nat} (d : Refutes (Γ + ⦃p,p⦄) f lo z) :
    Refutes (Γ + ⦃p⦄) f lo z := by
  intro C h
  apply d
  intro q hq
  apply h
  simpa using hq

def orLeft (a b : Nat) : Proof (wim a (wim (wn a) b)) := by
  let h : Context [wn a,a] a := .assumption (by simp)
  let hn : Context [wn a,a] (wn a) := .assumption (by simp)
  exact ((Context.mp h hn).explosion b).deduction.deduction.empty

def refutesAnd {Γ : LK.Sequent language} {p q : Proposition language}
    {f : Nat → Nat} {lo z : Nat}
    (d : Refutes (Γ + ⦃p⦄) f lo z) (e : Refutes (Γ + ⦃q⦄) f lo z) :
    Refutes (Γ + ⦃Semiformula.and p q⦄) f lo z := by
  intro C h
  let hx := fun r hr => h r (Multiset.mem_add.mpr (Or.inl hr))
  exact Context.mp (Context.andIntro (d.positive hx) (e.positive hx))
    (h (.and p q) (by simp))

def refutesOr {Γ : LK.Sequent language} {p q : Proposition language}
    {f : Nat → Nat} {lo z : Nat} (d : Refutes (Γ + ⦃p,q⦄) f lo z) :
    Refutes (Γ + ⦃Semiformula.or p q⦄) f lo z := by
  intro C h
  let ho := h (.or p q) (by simp)
  let hp := Context.mp ho (.closed (contrapose (orLeft (code p f lo z) (code q f lo z))))
  let hq := Context.mp ho (.closed (contrapose (Dominated.k (code q f lo z) (wn (code p f lo z)))))
  apply d
  intro r hr
  by_cases ep : r = p
  · subst r; exact hp
  · by_cases eq : r = q
    · subst r; exact hq
    · exact h r (Multiset.mem_add.mpr (Or.inl
        ((Multiset.mem_add.mp hr).resolve_right (by simp [ep,eq]))))

def refutesExs {Γ : LK.Sequent language} (p : Semiproposition language 1)
    (t : Semiterm language Nat 0) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i,f i < lo) (hz : lo+1+depth p ≤ z)
    (d : Refutes (Γ + ⦃instantiate p t⦄) f lo z) :
    Refutes (Γ + ⦃Semiformula.exs p⦄) f lo z := by
  intro C h
  let hp := d.positive (fun q hq => h q (Multiset.mem_add.mpr (Or.inl hq)))
  let hi := existentialInstance p t Fin.elim0 f lo z hlo (fun i => Fin.elim0 i) hf hz
  exact Context.mp (.mp hp (.closed hi)) (h (.exs p) (by simp))

theorem toNamed_shift (p : Proposition language) (f : Nat → Nat) (v lo : Nat) :
    toNamed (Semiformula.shift p) Fin.elim0 (shiftedLabels f v) lo =
      toNamed p Fin.elim0 f lo := by
  apply toNamed_rew
  intro t
  cases t with
  | bvar i => exact Fin.elim0 i
  | fvar i => rfl
  | func fn _ => nomatch fn

theorem toNamed_free (p : Semiproposition language 1) (f : Nat → Nat) (v lo : Nat) :
    toNamed (Semiformula.free p) Fin.elim0 (shiftedLabels f v) lo =
      toNamed p (Fin.cases v Fin.elim0) f lo := by
  apply toNamed_rew
  intro t
  cases t with
  | bvar i =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [Rew.free_bvar_last_zero,termLabel,shiftedLabels,Nat.cases_zero,Fin.cases_zero]
  | fvar i => rfl
  | func fn _ => nomatch fn

def negativeContextSupply (ps : List (Proposition language)) (f : Nat → Nat) (lo z : Nat)
    {C : List Nat} (h : ∀ p,p ∈ ps → Context C (wn (code p f lo z)))
    (a : Nat) (ha : a ∈ negativeContext ps Fin.elim0 f lo z) : Context C a := by
  cases ps with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons p ps =>
    by_cases e : a = wn (code p f lo z)
    · subst a; exact h p (by simp)
    · exact negativeContextSupply ps f lo z
        (fun q hq => h q (List.mem_cons_of_mem _ hq)) a
        ((List.mem_cons.mp ha).resolve_left e)

def refutesAll {Γ : LK.Sequent language} (tg : Γ.Traversal)
    (p : Semiproposition language 1) (f : Nat → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hf : ∀ i,f i < lo) (hlz : lo < z)
    (hz : ∀ q,q ∈ Γ → lo+1+depth q ≤ z)
    (d : Refutes (Rewriting.shifts Γ + ⦃p.free⦄) (shiftedLabels f lo) (lo+1) z) :
    Refutes (Γ + ⦃Semiformula.all p⦄) f lo z := by
  intro C h
  let K := negativeContext tg.toList Fin.elim0 f (lo+1) z
  have hs : ∀ q,q ∈ Rewriting.shifts Γ →
      Context K (wn (code q (shiftedLabels f lo) (lo+1) z)) := by
    intro q hq
    let pre := tg.getPreimage (f := Semiformula.shift) hq
    have hm : pre.val ∈ tg.toList := by
      exact (congrArg (fun xs : Multiset (Proposition language) => pre.val ∈ xs)
        tg.coe_toList).mpr pre.property.1
    have hc : Context K (wn (code pre.val f (lo+1) z)) :=
      .assumption (List.mem_map.mpr ⟨pre.val,hm,rfl⟩)
    rw [← pre.property.2]
    simpa only [code,toNamed_shift] using hc
  let body := d.positive hs
  have hb : Context K (relationalCode z
      (toNamed p (Fin.cases lo Fin.elim0) f (lo+1))) := by
    simpa only [code,toNamed_free] using body
  let hg := generalizeNegativeContext tg.toList Fin.elim0 f (lo+1) lo z hlo
    (by omega) (fun i => Fin.elim0 i) (fun i => Nat.ne_of_lt (hf i)) (by omega) hb
  have hu : Context C (code (.all p) f lo z) := hg.cut
    (negativeContextSupply tg.toList f (lo+1) z (fun q hq => by
      have hm : q ∈ Γ := by rw [← tg.coe_toList]; exact hq
      let hr := reallocation q Fin.elim0 f lo (lo+1) z hlo (by omega)
        (fun i => Fin.elim0 i) (fun i => by simpa using hf i)
        (by have hh := hz q hm; omega)
      exact Context.mp (h q (Multiset.mem_add.mpr (Or.inl hm))) (.closed (Bi.neg hr).1)))
  exact Context.mp hu (h (.all p) (by simp))

/-- Every actual Foundation LK logical derivation is compiled into a finite
actual-basis context proof. The numeric budget reserves the relational binder
and all eigenvariables; no semantic validity or completeness is used. -/
def compileLK {Γ : LK.Sequent language} (d : LK.Derivation Γ)
    (f : Nat → Nat) (lo z : Nat) (hlo : 0 < lo) (hf : ∀ i,f i < lo)
    (hz : lo + lkBudget d ≤ z) : Refutes Γ f lo z := by
  cases d with
  | identity r ts => exact refutesIdentity r ts f lo z
  | verum => exact refutesVerum f lo z
  | cut p q =>
    have hp : lkBudget p ≤ lkBudget (.cut p q) :=
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
    have hq : lkBudget q ≤ lkBudget (.cut p q) :=
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    exact fun {C} => refutesCut (compileLK p f lo z hlo hf (by omega))
      (compileLK q f lo z hlo hf (by omega))
  | contraction p =>
    have hp : lkBudget p ≤ lkBudget (.contraction p) := Nat.le_max_right _ _
    exact fun {C} => refutesContraction (compileLK p f lo z hlo hf (by omega))
  | @weakening Γ φ p =>
    have hp : lkBudget p ≤ lkBudget (.weakening (φ := φ) p) := Nat.le_max_right _ _
    exact fun {C} => refutesWeakening (p := φ) (compileLK p f lo z hlo hf (by omega))
  | or p =>
    have hp : lkBudget p ≤ lkBudget (.or p) := Nat.le_max_right _ _
    exact fun {C} => refutesOr (compileLK p f lo z hlo hf (by omega))
  | and p q =>
    have hp : lkBudget p ≤ lkBudget (.and p q) :=
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
    have hq : lkBudget q ≤ lkBudget (.and p q) :=
      (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
    exact fun {C} => refutesAnd (compileLK p f lo z hlo hf (by omega))
      (compileLK q f lo z hlo hf (by omega))
  | @all Γ p d =>
    have hd : lkBudget d + 1 ≤ lkBudget (.all d) := Nat.le_max_right _ _
    have hpos : 0 < lkBudget (.all d) := by
      have h := depth_lt_lkBudget (.all d) (p := .all p) (Multiset.mem_add.mpr (Or.inr (by exact Multiset.mem_singleton_self _)))
      omega
    apply refutesAll (LK.Derivation.all d).traversal.remove p f lo z hlo hf (by omega)
    · intro q hq
      have h := depth_lt_lkBudget (.all d) (Multiset.mem_add.mpr (Or.inl hq))
      omega
    · exact compileLK d (shiftedLabels f lo) (lo+1) z (by omega)
        (fun i => by cases i with
         | zero => simp [shiftedLabels]
         | succ i => simpa [shiftedLabels] using Nat.lt_trans (hf i) (Nat.lt_succ_self lo))
        (by omega)
  | @exs Γ p t d =>
    have hd : lkBudget d + 1 ≤ lkBudget (.exs d) := Nat.le_max_right _ _
    apply refutesExs p t f lo z hlo hf
    · have h := depth_lt_lkBudget (.exs d) (p := .exs p) (Multiset.mem_add.mpr (Or.inr (by exact Multiset.mem_singleton_self _)))
      simp only [depth] at h
      omega
    · have hi : instantiate p t = p/[t] := by
        apply congrArg (fun ω => Semiformula.rewAux ω p)
        apply congrArg Rew.subst
        funext i
        have hh : i = 0 := Fin.eq_zero i
        subst i
        rfl
      rw [hi]
      exact fun {C} => compileLK d f lo z hlo hf (by omega)
termination_by structural d

def compileSingleton (p : Proposition language) (d : LK.Derivation ⦃p⦄)
    (f : Nat → Nat) (lo : Nat) (hlo : 0 < lo) (hf : ∀ i,f i < lo) :
    Proof (code p f lo (lo + lkBudget d)) := by
  let h : Refutes ⦃p⦄ f lo (lo + lkBudget d) := fun {C} => compileLK d f lo (lo + lkBudget d) hlo hf (Nat.le_refl _)
  have r : Context [wn (code p f lo (lo + lkBudget d))] 1 := h fun q hq => by
    have e : q = p := by simpa using hq
    subst q
    exact .assumption (by simp)
  exact r.deduction.dne.empty

#print axioms compileLK
#print axioms compileSingleton
end PA196.Logic.Relational.Source

