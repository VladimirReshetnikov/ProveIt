/-
  Calculus.lean

  GENERIC classical natural deduction over the formulas of Fol.lean, and
  its proof theory — independent of any particular theory:

   - the calculus `Prov : List Form → Form → Prop` (assumption,
     intro/elim rules for the connectives and quantifiers, excluded
     middle, equality reflexivity and the Leibniz rule `P_eqElim`);
   - admissible rules: weakening, deduction, ex falso, proof by
     contradiction, double negation elimination, cut, and renaming
     admissibility `Prov_rename`;
   - consistency `Con` with the Lindenbaum step `Con_cons_or`;
   - the derived equality kit (symmetry, transitivity, congruence);
   - eigenvariable generalization and the Henkin-witness core lemmas;
   - SOUNDNESS: `Prov G a → ∀ e, (e ⊨ G) → Sat e a` over any
     structure (V, mem).

  Lean 4 port of the Rocq/Coq development `Logic/FirstOrder/Coq/Calculus.v`.
-/
import FirstOrder.Fol

namespace SetTheory

open Form

/-!
The natural-deduction calculus.  Terms are variables only (the signature is
purely relational), so quantifier instantiation substitutes a variable for
de Bruijn 0 — which is just a renaming.
-/

inductive Prov : List Form → Form → Prop
  | P_ass    : ∀ G a, a ∈ G → Prov G a
  | P_impI   : ∀ G a b, Prov (a :: G) b → Prov G (fImp a b)
  | P_impE   : ∀ G a b, Prov G (fImp a b) → Prov G a → Prov G b
  | P_botE   : ∀ G a, Prov G fBot → Prov G a
  | P_lem    : ∀ G a, Prov G (fOr a (fImp a fBot))
  | P_andI   : ∀ G a b, Prov G a → Prov G b → Prov G (fAnd a b)
  | P_andE1  : ∀ G a b, Prov G (fAnd a b) → Prov G a
  | P_andE2  : ∀ G a b, Prov G (fAnd a b) → Prov G b
  | P_orI1   : ∀ G a b, Prov G a → Prov G (fOr a b)
  | P_orI2   : ∀ G a b, Prov G b → Prov G (fOr a b)
  | P_orE    : ∀ G a b c, Prov G (fOr a b) → Prov (a :: G) c → Prov (b :: G) c →
               Prov G c
  | P_allI   : ∀ G a, Prov (G.map (rename Nat.succ)) a → Prov G (fAll a)
  | P_allE   : ∀ G a k, Prov G (fAll a) → Prov G (rename (inst k) a)
  | P_exI    : ∀ G a k, Prov G (rename (inst k) a) → Prov G (fEx a)
  | P_exE    : ∀ G a c, Prov G (fEx a) →
               Prov (a :: G.map (rename Nat.succ)) (rename Nat.succ c) → Prov G c
  | P_eqRefl : ∀ G k, Prov G (fEq k k)
  /-- Proper Leibniz: from `i = j` and `a[0:=i]` infer `a[0:=j]` (`a` is the
  property with a hole at de Bruijn 0). Gives symmetry/transitivity/congruence. -/
  | P_eqElim : ∀ G i j a,
      Prov G (fEq i j) → Prov G (rename (inst i) a) → Prov G (rename (inst j) a)

/-! ## [1] Proof-theory infrastructure -/

/-- Context inclusion is preserved by consing the same head. -/
theorem cons_sub {a : Form} {G G' : List Form} (hsub : ∀ x ∈ G, x ∈ G') :
    ∀ x ∈ a :: G, x ∈ a :: G' := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_cons.mpr (Or.inl rfl)
  · exact List.mem_cons.mpr (Or.inr (hsub x hx))

/-- Context inclusion is preserved by mapping. -/
theorem mem_map_sub {f : Form → Form} {G G' : List Form}
    (hsub : ∀ x ∈ G, x ∈ G') : ∀ x ∈ G.map f, x ∈ G'.map f := by
  intro x hx
  rw [List.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hsub y hy, rfl⟩

/-- Weakening: enlarging the context preserves provability. -/
theorem Prov_weaken {G : List Form} {a : Form} (h : Prov G a) :
    ∀ G', (∀ x ∈ G, x ∈ G') → Prov G' a := by
  induction h with
  | P_ass G a hin => intro G' hsub; exact .P_ass _ _ (hsub a hin)
  | P_impI G a b _ ih => intro G' hsub; exact .P_impI _ _ _ (ih _ (cons_sub hsub))
  | P_impE G a b _ _ ihab iha =>
    intro G' hsub; exact .P_impE _ a b (ihab _ hsub) (iha _ hsub)
  | P_botE G a _ ih => intro G' hsub; exact .P_botE _ a (ih _ hsub)
  | P_lem G a => intro G' hsub; exact .P_lem _ _
  | P_andI G a b _ _ iha ihb =>
    intro G' hsub; exact .P_andI _ _ _ (iha _ hsub) (ihb _ hsub)
  | P_andE1 G a b _ ih => intro G' hsub; exact .P_andE1 _ a b (ih _ hsub)
  | P_andE2 G a b _ ih => intro G' hsub; exact .P_andE2 _ a b (ih _ hsub)
  | P_orI1 G a b _ ih => intro G' hsub; exact .P_orI1 _ _ _ (ih _ hsub)
  | P_orI2 G a b _ ih => intro G' hsub; exact .P_orI2 _ _ _ (ih _ hsub)
  | P_orE G a b c _ _ _ ihor iha ihb =>
    intro G' hsub
    exact .P_orE _ a b c (ihor _ hsub) (iha _ (cons_sub hsub)) (ihb _ (cons_sub hsub))
  | P_allI G a _ ih =>
    intro G' hsub; exact .P_allI _ _ (ih _ (mem_map_sub hsub))
  | P_allE G a k _ ih => intro G' hsub; exact .P_allE _ a k (ih _ hsub)
  | P_exI G a k _ ih => intro G' hsub; exact .P_exI _ a k (ih _ hsub)
  | P_exE G a c _ _ ihex ihbody =>
    intro G' hsub
    exact .P_exE _ a c (ihex _ hsub) (ihbody _ (cons_sub (mem_map_sub hsub)))
  | P_eqRefl G k => intro G' hsub; exact .P_eqRefl _ k
  | P_eqElim G i j a _ _ iheq iha =>
    intro G' hsub; exact .P_eqElim _ i j a (iheq _ hsub) (iha _ hsub)

/-- A handy corollary: prepend an unused hypothesis. -/
theorem Prov_cons {G : List Form} {a b : Form} (h : Prov G b) : Prov (a :: G) b :=
  Prov_weaken h _ (fun _ hx => List.mem_cons.mpr (Or.inr hx))

/-- The head of the context is provable. -/
theorem Prov_ass_head {G : List Form} {a : Form} : Prov (a :: G) a :=
  .P_ass _ _ (List.mem_cons.mpr (Or.inl rfl))

/-- Disjunction elimination in implication form.  This derived rule is often
more convenient for lifting finite derivations into relative provability,
where all premises naturally share one context. -/
theorem Prov_orE_imp {G : List Form} {a b c : Form}
    (hor : Prov G (fOr a b))
    (ha : Prov G (fImp a c))
    (hb : Prov G (fImp b c)) : Prov G c :=
  .P_orE G a b c hor
    (.P_impE (a :: G) a c (Prov_cons ha)
      Prov_ass_head)
    (.P_impE (b :: G) b c (Prov_cons hb)
      Prov_ass_head)

/-- Proof by contradiction. -/
theorem Prov_byContra {G : List Form} {a : Form}
    (h : Prov (fImp a fBot :: G) fBot) : Prov G a :=
  .P_orE _ a (fImp a fBot) a (.P_lem _ _)
    Prov_ass_head
    (.P_botE _ a h)

/-- Double-negation elimination. -/
theorem Prov_dne {G : List Form} {a : Form}
    (h : Prov G (fImp (fImp a fBot) fBot)) : Prov G a :=
  Prov_byContra (.P_impE _ (fImp a fBot) fBot (Prov_cons h)
    Prov_ass_head)

/-! ## [2] Consistency -/

def Con (G : List Form) : Prop := ¬ Prov G fBot

/-! ### Equality kit: the proper Leibniz rule makes equality an equivalence
with full congruence. -/

theorem Prov_eq_sym (G : List Form) (i j : Nat) (h : Prov G (fEq i j)) :
    Prov G (fEq j i) :=
  Prov.P_eqElim G i j (fEq 0 (i+1)) h (Prov.P_eqRefl G i)

theorem Prov_eq_trans (G : List Form) (i j k : Nat)
    (h1 : Prov G (fEq i j)) (h2 : Prov G (fEq j k)) : Prov G (fEq i k) :=
  Prov.P_eqElim G j k (fEq (i+1) 0) h2 h1

theorem Prov_mem_cong1 (G : List Form) (i j k : Nat)
    (h1 : Prov G (fEq i j)) (h2 : Prov G (fMem i k)) : Prov G (fMem j k) :=
  Prov.P_eqElim G i j (fMem 0 (k+1)) h1 h2

theorem Prov_mem_cong2 (G : List Form) (i j k : Nat)
    (h1 : Prov G (fEq i j)) (h2 : Prov G (fMem k i)) : Prov G (fMem k j) :=
  Prov.P_eqElim G i j (fMem (k+1) 0) h1 h2

/-! ## [4a] Renaming admissibility for the calculus -/

theorem map_rename_up_S (r : Nat → Nat) (G : List Form) :
    (G.map (rename Nat.succ)).map (rename (up r))
      = (G.map (rename r)).map (rename Nat.succ) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro x _
  show rename (up r) (rename Nat.succ x) = rename Nat.succ (rename r x)
  rw [rename_comp, rename_comp]
  exact rename_ext x _ _ (fun n => rfl)

theorem Prov_rename {G : List Form} {phi : Form} (h : Prov G phi) :
    ∀ r, Prov (G.map (rename r)) (rename r phi) := by
  induction h with
  | P_ass G a hin => intro r; exact .P_ass _ _ (List.mem_map_of_mem hin)
  | P_impI G a b _ ih => intro r; exact .P_impI _ _ _ (ih r)
  | P_impE G a b _ _ ihab iha =>
    intro r; exact .P_impE _ (rename r a) (rename r b) (ihab r) (iha r)
  | P_botE G a _ ih => intro r; exact .P_botE _ (rename r a) (ih r)
  | P_lem G a => intro r; exact .P_lem _ _
  | P_andI G a b _ _ iha ihb => intro r; exact .P_andI _ _ _ (iha r) (ihb r)
  | P_andE1 G a b _ ih =>
    intro r; exact .P_andE1 _ (rename r a) (rename r b) (ih r)
  | P_andE2 G a b _ ih =>
    intro r; exact .P_andE2 _ (rename r a) (rename r b) (ih r)
  | P_orI1 G a b _ ih => intro r; exact .P_orI1 _ _ _ (ih r)
  | P_orI2 G a b _ ih => intro r; exact .P_orI2 _ _ _ (ih r)
  | P_orE G a b c _ _ _ ihor iha ihb =>
    intro r
    exact .P_orE _ (rename r a) (rename r b) (rename r c) (ihor r) (iha r) (ihb r)
  | P_allI G a _ ih =>
    intro r
    apply Prov.P_allI
    rw [← map_rename_up_S r G]
    exact ih (up r)
  | P_allE G a k _ ih =>
    intro r
    have heq := rename_inst_push a r k
    rw [heq]
    exact .P_allE _ (rename (up r) a) (r k) (ih r)
  | P_exI G a k _ ih =>
    intro r
    apply Prov.P_exI _ (rename (up r) a) (r k)
    have heq := rename_inst_push a r k
    rw [← heq]
    exact ih r
  | P_exE G a c _ _ ihex ihbody =>
    intro r
    apply Prov.P_exE _ (rename (up r) a) (rename r c)
    · exact ihex r
    · have hc : rename Nat.succ (rename r c) = rename (up r) (rename Nat.succ c) := by
        rw [rename_comp, rename_comp]
        exact rename_ext c _ _ (fun n => rfl)
      have h2 := ihbody (up r)
      simp only [List.map_cons] at h2
      rw [map_rename_up_S r G] at h2
      rw [hc]
      exact h2
  | P_eqRefl G k => intro r; exact .P_eqRefl _ (r k)
  | P_eqElim G i j a _ _ iheq iha =>
    intro r
    have heqj := rename_inst_push a r j
    have heqi := rename_inst_push a r i
    rw [heqj]
    apply Prov.P_eqElim _ (r i) (r j) (rename (up r) a) (iheq r)
    rw [← heqi]
    exact iha r

/-- Eigenvariable generalization: from `G ⊢ a[w/0]` with `w` fresh,
`G` shifted `⊢ a`. -/
theorem generalize_fresh (G : List Form) (a : Form) (w : Nat)
    (hwG : ∀ g ∈ G, ¬ Free w g) (hwa : ¬ Free (w+1) a)
    (hp : Prov G (rename (inst w) a)) : Prov (G.map (rename Nat.succ)) a := by
  have hr := Prov_rename hp (rho_w w)
  rw [rho_inst a w hwa] at hr
  rw [map_rho_S G w hwG] at hr
  exact hr

/-- Context exchange (same elements ⇒ same provability). -/
theorem Prov_exch {G G' : List Form} {phi : Form}
    (h : ∀ x, x ∈ G ↔ x ∈ G') (hp : Prov G phi) : Prov G' phi :=
  Prov_weaken hp G' (fun x hx => (h x).mp hx)

/-! ### The `Prov`-level cores of the Henkin lemmas, with an arbitrary fresh
witness. -/

theorem henkin_ex_core (G : List Form) (a : Form) (w : Nat)
    (hwa : ¬ Free (w+1) a) (hwG : ∀ g ∈ G, ¬ Free w g)
    (hbad : Prov (rename (inst w) a :: fEx a :: G) fBot) :
    Prov (fEx a :: G) fBot := by
  apply Prov.P_exE (fEx a :: G) a fBot
  · exact Prov_ass_head
  · have hr := Prov_rename hbad (rho_w w)
    simp only [List.map_cons] at hr
    rw [rho_inst a w hwa] at hr
    have e1 : rename (rho_w w) (fEx a) = rename Nat.succ (fEx a) := by
      show fEx (rename (up (rho_w w)) a) = fEx (rename (up Nat.succ) a)
      rw [rho_under a w hwa]
    rw [e1, map_rho_S G w hwG] at hr
    exact hr

theorem henkin_all_core (G : List Form) (a : Form) (w : Nat)
    (hwa : ¬ Free (w+1) a) (hwG : ∀ g ∈ G, ¬ Free w g)
    (hbad : Prov (fImp (rename (inst w) a) fBot :: fImp (fAll a) fBot :: G) fBot) :
    Prov (fImp (fAll a) fBot :: G) fBot := by
  have hbad' := Prov_byContra hbad
  have hwG' : ∀ g ∈ (fImp (fAll a) fBot :: G), ¬ Free w g := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · intro hf
      rcases hf with hf | hf
      · exact hwa hf
      · exact hf
    · exact hwG g hg
  have hgen := generalize_fresh _ a w hwG' hwa hbad'
  exact .P_impE _ (fAll a) fBot Prov_ass_head
    (.P_allI _ a hgen)

/-! ## [4c] Cut: replacing assumptions by derivations -/

theorem Prov_cut {G : List Form} {phi : Form} (h : Prov G phi) :
    ∀ De, (∀ x ∈ G, Prov De x) → Prov De phi := by
  induction h with
  | P_ass G a hin => intro De hD; exact hD a hin
  | P_impI G a b _ ih =>
    intro De hD
    apply Prov.P_impI
    apply ih
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Prov_ass_head
    · exact Prov_cons (hD x hx)
  | P_impE G a b _ _ ihab iha =>
    intro De hD; exact .P_impE _ a b (ihab De hD) (iha De hD)
  | P_botE G a _ ih => intro De hD; exact .P_botE _ a (ih De hD)
  | P_lem G a => intro De hD; exact .P_lem _ _
  | P_andI G a b _ _ iha ihb =>
    intro De hD; exact .P_andI _ _ _ (iha De hD) (ihb De hD)
  | P_andE1 G a b _ ih => intro De hD; exact .P_andE1 _ a b (ih De hD)
  | P_andE2 G a b _ ih => intro De hD; exact .P_andE2 _ a b (ih De hD)
  | P_orI1 G a b _ ih => intro De hD; exact .P_orI1 _ _ _ (ih De hD)
  | P_orI2 G a b _ ih => intro De hD; exact .P_orI2 _ _ _ (ih De hD)
  | P_orE G a b c _ _ _ ihor iha ihb =>
    intro De hD
    apply Prov.P_orE _ a b c (ihor De hD)
    · apply iha
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Prov_ass_head
      · exact Prov_cons (hD x hx)
    · apply ihb
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Prov_ass_head
      · exact Prov_cons (hD x hx)
  | P_allI G a _ ih =>
    intro De hD
    apply Prov.P_allI
    apply ih
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨x0, hx0, rfl⟩ := hx
    exact Prov_rename (hD x0 hx0) Nat.succ
  | P_allE G a k _ ih => intro De hD; exact .P_allE _ a k (ih De hD)
  | P_exI G a k _ ih => intro De hD; exact .P_exI _ a k (ih De hD)
  | P_exE G a c _ _ ihex ihbody =>
    intro De hD
    apply Prov.P_exE _ a c (ihex De hD)
    apply ihbody
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Prov_ass_head
    · rw [List.mem_map] at hx
      obtain ⟨x0, hx0, rfl⟩ := hx
      exact Prov_cons (Prov_rename (hD x0 hx0) Nat.succ)
  | P_eqRefl G k => intro De hD; exact .P_eqRefl _ k
  | P_eqElim G i j a _ _ iheq iha =>
    intro De hD; exact .P_eqElim _ i j a (iheq De hD) (iha De hD)

/-! ## Soundness for Tarski semantics -/

section Soundness

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- Environment lemma for the context shift. -/
theorem shift_sat (G : List Form) (e : Nat → V) (d : V)
    (hG : ∀ x ∈ G, Sat mem e x) :
    ∀ y ∈ G.map (rename Nat.succ), Sat mem (scons d e) y := by
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨x, hxin, rfl⟩ := hy
  exact (Sat_rename_ext x Nat.succ _ _ (fun n => rfl)).mpr (hG x hxin)

theorem soundness {G : List Form} {a : Form} (h : Prov G a) :
    ∀ e : Nat → V, (∀ x ∈ G, Sat mem e x) → Sat mem e a := by
  induction h with
  | P_ass G a hin => intro e hG; exact hG a hin
  | P_impI G a b _ ih =>
    intro e hG
    show Sat mem e a → Sat mem e b
    intro ha
    apply ih e
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact hG x hx
  | P_impE G a b _ _ ihab iha => intro e hG; exact (ihab e hG) (iha e hG)
  | P_botE G a _ ih => intro e hG; exact (ih e hG).elim
  | P_lem G a =>
    intro e hG
    show Sat mem e a ∨ (Sat mem e a → False)
    exact Classical.em _
  | P_andI G a b _ _ iha ihb => intro e hG; exact ⟨iha e hG, ihb e hG⟩
  | P_andE1 G a b _ ih => intro e hG; exact (ih e hG).1
  | P_andE2 G a b _ ih => intro e hG; exact (ih e hG).2
  | P_orI1 G a b _ ih => intro e hG; exact Or.inl (ih e hG)
  | P_orI2 G a b _ ih => intro e hG; exact Or.inr (ih e hG)
  | P_orE G a b c _ _ _ ihor iha ihb =>
    intro e hG
    rcases ihor e hG with ha | hb
    · apply iha e
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact hG x hx
    · apply ihb e
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hb
      · exact hG x hx
  | P_allI G a _ ih =>
    intro e hG
    show ∀ d, Sat mem (scons d e) a
    intro d
    exact ih (scons d e) (shift_sat G e d hG)
  | P_allE G a k _ ih =>
    intro e hG
    exact (Sat_rename_ext a (inst k) _ _ (inst_env k e)).mpr (ih e hG (e k))
  | P_exI G a k _ ih =>
    intro e hG
    refine ⟨e k, ?_⟩
    have := ih e hG
    exact (Sat_rename_ext a (inst k) _ _ (inst_env k e)).mp this
  | P_exE G a c _ _ ihex ihbody =>
    intro e hG
    obtain ⟨d, hd⟩ := ihex e hG
    have hc : Sat mem (scons d e) (rename Nat.succ c) := by
      apply ihbody (scons d e)
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hd
      · exact shift_sat G e d hG y hy
    exact (Sat_rename_ext c Nat.succ _ _ (fun n => rfl)).mp hc
  | P_eqRefl G k => intro e hG; exact rfl
  | P_eqElim G i j a _ _ iheq iha =>
    intro e hG
    have hij : e i = e j := iheq e hG
    refine (Sat_rename_ext a (inst j) _ _ (inst_env j e)).mpr ?_
    have ha := iha e hG
    have ha' := (Sat_rename_ext a (inst i) _ _ (inst_env i e)).mp ha
    rw [hij] at ha'
    exact ha'

end Soundness

end SetTheory
