module
public import PA196.Logic.Relational.SeparationSchema
public import PA196.Logic.Relational.SourceNegation
@[expose] public section

namespace PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)
theorem named_replace_of_names_false (p : Named) (x y : Nat) (h : p.names x = false) :
    p.replace x y = p := by
  induction p with
  | truth => rfl
  | neg p ih => exact congrArg M6.PA.NativeCalculus.Named.neg (ih h)
  | imp p q ihp ihq =>
    simp only [M6.PA.NativeCalculus.Named.names,Bool.or_eq_false_iff] at h
    simp only [M6.PA.NativeCalculus.Named.replace,ihp h.1,ihq h.2]
  | mem a b | eq a b =>
    simp only [M6.PA.NativeCalculus.Named.names,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at h
    simp [M6.PA.NativeCalculus.Named.replace,renameLabel,Ne.symm h.1,Ne.symm h.2]
  | all a p ih =>
    simp only [M6.PA.NativeCalculus.Named.names,Bool.or_eq_false_iff] at h
    simp only [M6.PA.NativeCalculus.Named.replace,ih h.2]

theorem paddedOutput_fresh (a b z : Nat) (p : Named) :
    p.names (relationalCode z (paddedProperty a b z p)) = false := by
  let c := relationalCode z (paddedProperty a b z p)
  have hpair := PA196.Logic.pair_bounds (relationalCode z p) (paddingLabel a b z p)
  have hc : p.encode < c := by
    simp only [c,paddedProperty,relationalCode,PA196.Logic.wal,paddingLabel]
    dsimp [paddingLabel] at hpair
    omega
  cases h : p.names c with
  | false => rfl
  | true => have hh := p.names_bound c h; omega

def separationAtName (a b c z : Nat) (p : Named)
    (ha : a < z) (hb : b < z) (hc : c < z)
    (hca : c ≠ a) (hcb : c ≠ b)
    (hpz : p.names z = false) (hpc : p.names c = false) :
    Proof (wex c (wal b (iffCode (wel c b) (wa (wel a b) (relationalCode z p))))) := by
  let d := separationOutput a b z p
  have hd : z < d := (paddedCode_bounds a b z (separationProperty a b p)).2.2
  have hpd : p.names d = false := by
    have h := paddedOutput_fresh a b z (separationProperty a b p)
    simp only [separationProperty,namedAnd,M6.PA.NativeCalculus.Named.names,Bool.or_eq_false_iff] at h
    exact h.2
  let body : Named := .all b (namedAnd
    (.imp (.mem d b) (namedAnd (.mem a b) p))
    (.imp (namedAnd (.mem a b) p) (.mem d b)))
  have hdB : p.binders d = false := names_binders_false p d hpd
  let alpha := relationalUniversalAlpha (.neg body) z d c (by omega)
    (by simp [body,namedAnd,M6.PA.NativeCalculus.Named.names,hpz]; omega) (by omega) (by omega)
    (by simp [body,namedAnd,M6.PA.NativeCalculus.Named.binders,hdB]; omega)
    (by simp [body,namedAnd,M6.PA.NativeCalculus.Named.names,hpc,hca,hcb]; omega)
  let h := (Bi.neg alpha).1
  simpa only [body,namedAnd,M6.PA.NativeCalculus.Named.replace,relationalCode,named_replace_of_names_false p d c hpd,
    renameLabel,ite_true,if_neg (show b ≠ d by omega),if_neg (show a ≠ d by omega),
    iffCode,wa,wex] using PA196.Logic.Derivation.mp (actualSeparation a b z p) h

#print axioms separationAtName
end PA196.Logic.Relational
