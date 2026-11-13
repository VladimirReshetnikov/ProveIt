module
public import M6PA.Theory
public import M6PA.Calibration.ActualRelationalAlpha
@[expose] public section

/-! Bottom-up actual-basis finite freshening compiler for the restricted
relational image. The reserved equality label stays below newly allocated
binders and absent from all original names. This is external finite syntax. -/
namespace M6.PA.NativeCalculus.ActualBasis
theorem names_split (p : Named) (v : Nat) :
    p.names v = (p.free v || p.binders v) := by
  induction p with
  | truth | mem | eq => simp [Named.names,Named.free,Named.binders]
  | neg p ih => exact ih
  | imp p q ihp ihq =>
    simp only [Named.names,Named.free,Named.binders,ihp,ihq]
    cases p.free v <;> cases q.free v <;> cases p.binders v <;> cases q.binders v <;> rfl
  | all a p ih =>
    simp only [Named.names,Named.free,Named.binders,ih]
    cases v == a <;> cases p.free v <;> cases p.binders v <;> rfl

theorem replace_free_outside (p : Named) (x y v : Nat) (hvx : v ≠ x) (hvy : v ≠ y) :
    (p.replace x y).free v = p.free v := by
  have hl (a : Nat) : (v == renameLabel x y a) = (v == a) := by
    by_cases ha : a = x
    · simp [renameLabel,ha,hvx,hvy]
    · simp [renameLabel,ha]
  induction p with
  | truth => rfl
  | mem a b | eq a b => simp only [Named.replace,Named.free,hl]
  | neg p ih => exact ih
  | imp p q ihp ihq => simp only [Named.replace,Named.free,ihp,ihq]
  | all a p ih => simp only [Named.replace,Named.free,ih]

theorem freshen_free_below (p : Named) (lo v : Nat) (hv : v < lo) :
    (p.freshen lo).free v = p.free v := by
  induction p generalizing lo with
  | truth | mem | eq => rfl
  | neg p ih => exact ih lo hv
  | imp p q ihp ihq => simp [Named.freshen,Named.free,ihp lo hv,ihq lo hv]
  | all a p ih =>
    have hvlo : v ≠ lo := Nat.ne_of_lt hv
    have hvloB : (v == lo) = false := beq_eq_false_iff_ne.mpr hvlo
    by_cases hva : v = a
    · subst a
      simp only [Named.freshen,Named.free,hvloB,Bool.not_false,Bool.true_and,replace_free _ _ _ hvlo,beq_self_eq_true,Bool.not_true,Bool.false_and]
    · have hvaB : (v == a) = false := beq_eq_false_iff_ne.mpr hva
      simp only [Named.freshen,Named.free,hvloB,hvaB,Bool.not_false,Bool.true_and,
        replace_free_outside _ _ _ _ hva hvlo,ih (lo+1) (by omega)]

theorem freshen_names_below (p : Named) (lo v : Nat) (hv : v < lo) :
    (p.freshen lo).names v = p.free v := by
  rw [names_split,Named.freshen_binders_below p lo v hv,freshen_free_below p lo v hv]
  simp


def forallCongruence (x : Nat) {a b : Nat} (h : Proof (wim a b)) :
    Proof (wim (wal x a) (wal x b)) := .mp (.all x h) (r2 x a b)

def implicationCongruence {a aa b bb : Nat} (p : Proof (wim aa a))
    (q : Proof (wim b bb)) : Proof (wim (wim a b) (wim aa bb)) :=
  (Context.implicationCongruence (Γ := []) (.closed p) (.closed q)).empty

def relationalFreshening (p : Named) (z lo : Nat)
    (hz : p.names z = false) (hzlo : z < lo)
    (hbound : ∀ v, p.names v = true → v < lo) :
    Proof (wim (relationalCode z p) (relationalCode z (p.freshen lo))) ×
    Proof (wim (relationalCode z (p.freshen lo)) (relationalCode z p)) :=
  match p with
  | .truth => ⟨identity 0,identity 0⟩
  | .mem a b => ⟨identity (wel a b),identity (wel a b)⟩
  | .eq a b => ⟨identity (neighborhoodEquality a b z),identity (neighborhoodEquality a b z)⟩
  | .neg p =>
    let hp := relationalFreshening p z lo hz hzlo hbound
    ⟨contrapose hp.2,contrapose hp.1⟩
  | .imp p q => by
    simp only [Named.names,Bool.or_eq_false_iff] at hz
    let hp := relationalFreshening p z lo hz.1 hzlo (fun v hv => hbound v (by simp [Named.names,hv]))
    let hq := relationalFreshening q z lo hz.2 hzlo (fun v hv => hbound v (by simp [Named.names,hv]))
    exact ⟨implicationCongruence hp.2 hq.1,implicationCongruence hp.1 hq.2⟩
  | .all a p => by
    simp only [Named.names,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hz
    have ha : a < lo := hbound a (by simp [Named.names])
    have hpbound (v : Nat) (hv : p.names v = true) : v < lo := hbound v (by simp [Named.names,hv])
    let hp := relationalFreshening p z (lo+1) hz.2 (by omega)
      (fun v hv => by have := hpbound v hv; omega)
    have hlo : p.names lo = false := by
      cases he : p.names lo with
      | false => rfl
      | true => have := hpbound lo he; omega
    have htarget : (p.freshen (lo+1)).names lo = false := by
      rw [freshen_names_below p (lo+1) lo (by omega)]
      exact names_free_false p lo hlo
    have hreserved : (p.freshen (lo+1)).names z = false := by
      rw [freshen_names_below p (lo+1) z (by omega)]
      exact names_free_false p z hz.2
    let halpha := relationalUniversalAlpha (p.freshen (lo+1)) z a lo (Nat.ne_of_lt ha)
      hreserved hz.1 (Nat.ne_of_lt hzlo)
      (p.freshen_binders_below (lo+1) a (by omega)) htarget
    exact ⟨implicationCompose (forallCongruence a hp.1) halpha.1,
      implicationCompose halpha.2 (forallCongruence a hp.2)⟩

def relationalCanonicalFreshening (p : Named) (z : Nat) (hz : p.names z = false) :
    Proof (wim (relationalCode z p) (relationalCode z (p.freshen (p.encode+z+1)))) ×
    Proof (wim (relationalCode z (p.freshen (p.encode+z+1))) (relationalCode z p)) :=
  relationalFreshening p z (p.encode+z+1) hz (by omega)
    (fun v hv => by have := p.names_bound v hv; omega)

#print axioms relationalFreshening
#print axioms relationalCanonicalFreshening
end M6.PA.NativeCalculus.ActualBasis

