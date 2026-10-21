/-- A proved implication lifts under any antecedent, by two detachments. -/
private theorem under_antecedent (z : A) {x y : A}
    (hxy : T (wim x y)) : T (wim (wim z x) (wim z y)) :=
  h.mp (d46 h x z y) (h.mp (d47 h x y z) hxy)

/-- Insert an independent antecedent into the basic application row. -/
private theorem insert_middle (a b c d : A) :
    T (wim a (wim b (wim (wim a c) (wim d c)))) :=
  h.mp (d47 h a (wim (wim a c) (wim d c)) b) (d16 h a c d)

/-- Contract the double application context without a deduction theorem. -/
private theorem application_contract (a b c : A) :
    T (wim (wim (wim (wim a b) b) (wim a c)) (wim a c)) :=
  h.mp (d22 h (wim (wim (wim a b) b) (wim a c)) (wim a c))
    (h.mp (d52 h (wim a c) a (wim (wim a b) b)
      (wim (wim (wim a b) b) (wim a c)))
      (h.mp (under_antecedent h (wim (wim a c) a) (d35 h a b))
        (d18 h a c)))

/-- Transport application into the antecedent of a proved implication. -/
private theorem application_transport (a b c : A) :
    T (wim (wim (wim (wim a b) b) c) (wim a c)) :=
  h.mp (d27 h a (wim (wim (wim a b) b) c) c)
    (h.mp (application_contract h a b
      (wim (wim (wim (wim a b) b) c) (wim a c)))
      (insert_middle h (wim (wim a b) b) a c a))

/-- Remove a repeated antecedent past two intervening arguments. -/
private theorem repeated_antecedent (a b c d : A) :
    T (wim (wim a (wim b (wim c (wim a d))))
      (wim b (wim c (wim a d)))) :=
  h.mp (d22 h (wim a (wim b (wim c (wim a d))))
    (wim b (wim c (wim a d))))
    (h.mp (h.rho8 a (wim a (wim b (wim c (wim a d))))
      (wim b (wim c (wim a d))) a (L.refl a))
      (h.mp (d38 h (wim c (wim a d)) a a b) (d23 h c a d)))

private theorem composition_seed (a b c : A) :
    T (wim (wim a b) (wim (wim b c) (wim a c))) := by
  have happ : T (wim (wim (wim a b) b)
      (wim (wim a b) (wim (wim b c) (wim a c)))) :=
    h.mp (d46 h b (wim a b) (wim (wim b c) (wim a c)))
      (insert_middle h b (wim a b) c a)
  exact h.mp (repeated_antecedent h a (wim a b) (wim b c) c)
    (h.mp (application_transport h a b
      (wim (wim a b) (wim (wim b c) (wim a c)))) happ)

end

section
variable {A : Type v} {L : Language A} {T : A → Prop}

private theorem withSeed (h : Restricted L T) (a : A) :
    WithSeed L (rho8 L a a a a) T where
  toRestricted := h
  truth := h.rho8 a a a a (L.refl a)

/-- Restricted rows and modus ponens alone derive every unrestricted row. -/
theorem rho8_all (h : Restricted L T) (a b c u : A) : T (rho8 L a b c u) :=
  d52 (withSeed h a) c u a b

theorem composition (h : Restricted L T) (a b c : A) :
    T (L.imp (L.imp a b) (L.imp (L.imp b c) (L.imp a c))) :=
  composition_seed (withSeed h a) a b c

/-- A proved implication lifts under any antecedent. -/
theorem lift_right (h : Restricted L T) {a b : A} (hab : T (L.imp a b)) (x : A) :
    T (L.imp (L.imp x a) (L.imp x b)) :=
  under_antecedent (withSeed h a) x hab

end
#print axioms rho8_all
#print axioms composition
#print axioms lift_right
end SetTheory.BusyBeaver.ZFC.DominatedImplication
