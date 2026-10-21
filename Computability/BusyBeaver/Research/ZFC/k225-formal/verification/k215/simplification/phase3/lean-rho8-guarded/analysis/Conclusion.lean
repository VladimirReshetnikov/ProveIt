/-! Deduction is used only after deriving K and S from the dominated rows. -/
private inductive Proof (T : Nat → Prop) : List Nat → Nat → Prop
  | ax {G a} : T a → Proof T G a
  | hyp {G a} : a ∈ G → Proof T G a
  | mp {G a b} : Proof T G (wim a b) → Proof T G a → Proof T G b

private theorem proof_sound {G : List Nat} {a : Nat} (d : Proof T G a)
    (hG : ∀ x, x ∈ G → T x) : T a := by
  induction d with
  | ax ht => exact ht
  | hyp hm => exact hG _ hm
  | mp _ _ ih1 ih2 => exact h.mp ih1 ih2

private theorem discharge_aux {a : Nat} {G' : List Nat} {b : Nat}
    (d : Proof T G' b) : ∀ G : List Nat, G' = a :: G → Proof T G (wim a b) := by
  induction d with
  | ax hb => intro G _; exact .mp (.ax (basisK h _ a)) (.ax hb)
  | hyp hm =>
      intro G hG
      subst hG
      cases List.mem_cons.mp hm with
      | inl he => subst he; exact .ax (basisI h _)
      | inr hin => exact .mp (.ax (basisK h _ a)) (.hyp hin)
  | mp _ _ ih1 ih2 =>
      intro G hG
      exact .mp (.mp (.ax (distribution h _ _ _)) (ih1 G hG)) (ih2 G hG)

private theorem discharge {G : List Nat} {a b : Nat}
    (d : Proof T (a :: G) b) : Proof T G (wim a b) :=
  discharge_aux h d G rfl

/-- Every unrestricted instance follows by deduction and Peirce's law. -/
theorem rho8_all (a b c u : Nat) : T (Code254.rho8 a b c u) := by
  let f := wim (wim c u) a
  let g := wim a c
  have hc : Proof T [wim c u, b, g, f] c :=
    .mp (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
      (.mp (.hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
        (.hyp (List.mem_cons_self ..)))
  have closedC : Proof T [b, g, f] c :=
    .mp (.ax (basisP h c u)) (discharge h hc)
  have result : Proof T [] (Code254.rho8 a b c u) :=
    discharge h (discharge h (discharge h closedC))
  exact proof_sound h result (by intro x hx; cases hx)
