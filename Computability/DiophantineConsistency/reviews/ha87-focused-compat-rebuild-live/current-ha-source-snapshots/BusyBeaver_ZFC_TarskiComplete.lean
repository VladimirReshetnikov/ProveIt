import FirstOrder.Fol
import BusyBeaver.ZFC.TarskiClean

/-!
Completeness of the machines' substitution-free Tarski calculus.

`completeness`: if a formula holds under every assignment in every model in
which every formula of `Ax` holds under every assignment, then it is a
theorem of the machine rows over `Ax`. Together with `soundness` this is
the logical half of every ZFC proof-search calibration: the eight rows
emitted by the calibrated machines are a complete first-order calculus.

The proof is a Henkin construction in which the terms are the labels
themselves:

* a Lindenbaum chain over an enumeration of formulas in which every
  formula is visited infinitely often; a rejected universal formula
  `∀a χ` (with `a` not rebound in `χ`) receives a fresh witness label at
  each visit, so it has witnesses above every bound;
* theory formulas are axioms of `Thm`, never hypotheses, so a witness only
  has to avoid the finitely many hypotheses chosen so far, and the theory
  needs no renaming;
* the model is the set of labels modulo provable equality, with membership
  read off the maximal set; `rho1` and the infinitely many witnesses give
  every class arbitrarily large representatives;
* the truth lemma is proved for clean formulas by induction on size,
  using `spec` for the universal case; `cl` and `cl_equiv` move the target
  formula and the closures of the theory axioms into the clean fragment.

The propositional basis enters only through the hypotheses `hC` and `hC0`
that the theorem predicates are classical; `Lukasiewicz.lean` derives them
from the row `rho8`.
-/

namespace SetTheory.BusyBeaver.ZFC.Tarski

open NF Kalmar

/-! ## Enumeration of formulas -/

def code : NF → Nat
  | rel i j => Cantor.toNat (0, Cantor.toNat (i, j))
  | NF.eq i j => Cantor.toNat (1, Cantor.toNat (i, j))
  | NF.bot => Cantor.toNat (2, 0)
  | imp a b => Cantor.toNat (3, Cantor.toNat (code a, code b))
  | all i a => Cantor.toNat (4, Cantor.toNat (i, code a))

def decode : Nat → Nat → NF
  | 0, _ => NF.bot
  | fuel + 1, n =>
    let p := (Cantor.ofNat n).2
    match (Cantor.ofNat n).1 with
    | 0 => rel (Cantor.ofNat p).1 (Cantor.ofNat p).2
    | 1 => NF.eq (Cantor.ofNat p).1 (Cantor.ofNat p).2
    | 2 => NF.bot
    | 3 => imp (decode fuel (Cantor.ofNat p).1) (decode fuel (Cantor.ofNat p).2)
    | 4 => all (Cantor.ofNat p).1 (decode fuel (Cantor.ofNat p).2)
    | _ + 5 => NF.bot

theorem decode_code (f : NF) : ∀ fuel, code f < fuel → decode fuel (code f) = f := by
  induction f with
  | rel _ _ | eq _ _ | bot =>
    intro fuel hlt
    match fuel with
    | 0 => omega
    | fuel + 1 => simp [code, decode, Cantor.ofNat_toNat]
  | imp a b iha ihb =>
    intro fuel hlt
    match fuel with
    | 0 => omega
    | fuel + 1 =>
      have b1 := Cantor.add_le_toNat 3 (Cantor.toNat (code a, code b))
      have b2 := Cantor.add_le_toNat (code a) (code b)
      simp only [code] at hlt
      simp [code, decode, Cantor.ofNat_toNat, iha fuel (by omega), ihb fuel (by omega)]
  | all i a ih =>
    intro fuel hlt
    match fuel with
    | 0 => omega
    | fuel + 1 =>
      have b1 := Cantor.add_le_toNat 4 (Cantor.toNat (i, code a))
      have b2 := Cantor.add_le_toNat i (code a)
      simp only [code] at hlt
      simp [code, decode, Cantor.ofNat_toNat, ih fuel (by omega)]

def enumF (n : Nat) : NF := decode (n + 1) n

theorem enumF_code (f : NF) : enumF (code f) = f :=
  decode_code f (code f + 1) (by omega)

/-! ## Monotonicity in the theory -/

theorem Thm.mono {B B' : NF → Prop} (hB : ∀ x, B x → B' x) {f : NF} (h : Thm B f) : Thm B' f := by
  induction h with
  | ax h => exact .ax (hB _ h)
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2
  | gen i _ ih => exact .gen i ih
  | rho8 => exact .rho8 ..
  | rho2 => exact .rho2 ..
  | rho4 => exact .rho4 ..
  | rho6 => exact .rho6 ..
  | rho1 => exact .rho1 ..
  | rho7 => exact .rho7 ..
  | rho5 => exact .rho5 ..
  | rho3 => exact .rho3 ..
  | vacRel a b c h1 h2 => exact .vacRel a b c h1 h2
  | vacEq a b c h1 h2 => exact .vacEq a b c h1 h2

/-! ## Generalization over hypotheses not containing the label -/

variable {Ax : NF → Prop}

theorem der_gen (hC : Classical NF.imp NF.bot (Thm Ax)) (c : Nat) {G : List NF} {x : NF}
    (d : Der NF.imp (Thm Ax) G x) (hG : ∀ g, g ∈ G → ¬ Occurs c g) :
    Der NF.imp (Thm Ax) G (all c x) := by
  induction d with
  | ax h => exact .ax (.gen c h)
  | hyp hm => exact .mp (.ax (vac_of_not_occurs hC c _ (hG _ hm))) (.hyp hm)
  | mp _ _ ih1 ih2 => exact .mp (.mp (.ax (.rho2 c _ _)) ih1) ih2

/-! ## Consistent hypothesis lists -/

def Cons (Ax : NF → Prop) (G : List NF) : Prop := ¬ Der NF.imp (Thm Ax) G NF.bot

section Lists

variable (hC : Classical NF.imp NF.bot (Thm Ax))
include hC

theorem cons_neg {G : List NF} {p : NF} (hG : Cons Ax G) (hp : ¬ Cons Ax (p :: G)) :
    Cons Ax (neg p :: G) := by
  intro d
  exact hG (.mp (deduction hC d) (deduction hC (Classical.byContradiction hp)))

/-- Adding a fresh witness of a refuted universal formula keeps consistency. -/
theorem cons_witness {G : List NF} {a c : Nat} {χ : NF}
    (hG : Cons Ax (neg (all a χ) :: G)) (hb : ¬ Bound a χ) (hca : c ≠ a)
    (hcχ : ¬ Occurs c χ) (hcG : ∀ g, g ∈ G → ¬ Occurs c g) :
    Cons Ax (neg (rn a c χ) :: neg (all a χ) :: G) := by
  intro d
  apply hG
  let G' := neg (all a χ) :: G
  have hfresh : ∀ g, g ∈ G' → ¬ Occurs c g := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp only [neg, Occurs]
      exact fun o => o.elim (fun o => o.elim hca hcχ) id
    · exact hcG g hg
  have d1 : Der NF.imp (Thm Ax) G' (rn a c χ) :=
    .mp (.ax (dne hC _)) (deduction hC d)
  exact .mp (.hyp (List.mem_cons_self ..))
    (.mp (.ax (alpha_bwd hC hca hb hcχ)) (der_gen hC c d1 hfresh))

end Lists

/-! ## The Lindenbaum chain -/

def topL : List NF → Nat
  | [] => 0
  | g :: G => max (top g) (topL G)

theorem top_le_topL {g : NF} : ∀ {G : List NF}, g ∈ G → top g ≤ topL G
  | _ :: G, h => by
      cases List.mem_cons.mp h with
      | inl he => subst he; simp only [topL]; omega
      | inr h => have := top_le_topL h; simp only [topL]; omega

open Classical in
/-- What a rejected formula contributes. -/
noncomputable def reject (G : List NF) (m : Nat) : NF → List NF
  | all a χ =>
      if Bound a χ then neg (all a χ) :: G
      else neg (rn a (max (topL (all a χ :: G)) m) χ) :: neg (all a χ) :: G
  | p => neg p :: G

theorem neg_mem_reject (G : List NF) (m : Nat) (p : NF) : neg p ∈ reject G m p := by
  cases p with
  | all a χ =>
      simp only [reject]
      split
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  | _ => exact List.mem_cons_self ..

theorem sub_reject (G : List NF) (m : Nat) (p : NF) : ∀ g, g ∈ G → g ∈ reject G m p := by
  intro g hg
  cases p with
  | all a χ =>
      simp only [reject]
      split
      · exact List.mem_cons_of_mem _ hg
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg)
  | _ => exact List.mem_cons_of_mem _ hg

open Classical in
noncomputable def step (Ax : NF → Prop) (G : List NF) (m : Nat) : List NF :=
  if Cons Ax (enumF (Cantor.ofNat m).1 :: G) then enumF (Cantor.ofNat m).1 :: G
  else reject G m (enumF (Cantor.ofNat m).1)

noncomputable def chain (Ax : NF → Prop) (f0 : NF) : Nat → List NF
  | 0 => [neg f0]
  | m + 1 => step Ax (chain Ax f0 m) m

theorem sub_step (G : List NF) (m : Nat) : ∀ g, g ∈ G → g ∈ step Ax G m := by
  intro g hg
  unfold step
  split
  · exact List.mem_cons_of_mem _ hg
  · exact sub_reject G m _ g hg

theorem chain_mono (f0 : NF) {m m' : Nat} (h : m ≤ m') :
    ∀ g, g ∈ chain Ax f0 m → g ∈ chain Ax f0 m' := by
  induction h with
  | refl => exact fun _ hg => hg
  | step _ ih => exact fun g hg => sub_step _ _ g (ih g hg)

section Chain

variable (hC : Classical NF.imp NF.bot (Thm Ax)) (f0 : NF)
include hC

theorem step_cons {G : List NF} (m : Nat) (hG : Cons Ax G) : Cons Ax (step Ax G m) := by
  unfold step
  split
  · assumption
  · rename_i hp
    have hn := cons_neg hC hG hp
    generalize enumF (Cantor.ofNat m).1 = p at hp hn ⊢
    cases p with
    | all a χ =>
        simp only [reject]
        split
        · exact hn
        · rename_i hb
          let c := max (topL (all a χ :: G)) m
          have hc : top (all a χ) ≤ c := by
            have := top_le_topL (g := all a χ) (G := all a χ :: G) (List.mem_cons_self ..)
            omega
          simp only [top] at hc
          refine cons_witness hC hn hb (by omega) (not_occurs_of_top_le (by omega))
            fun g hg => not_occurs_of_top_le ?_
          have := top_le_topL (g := g) (G := all a χ :: G) (List.mem_cons_of_mem _ hg)
          omega
    | _ => exact hn

theorem chain_cons (h0 : Cons Ax [neg f0]) : ∀ m, Cons Ax (chain Ax f0 m)
  | 0 => h0
  | m + 1 => step_cons hC m (chain_cons h0 m)

end Chain

/-! ## The maximal set -/

def Gam (Ax : NF → Prop) (f0 : NF) (g : NF) : Prop := ∃ m, g ∈ chain Ax f0 m

section Maximal

variable (hC : Classical NF.imp NF.bot (Thm Ax)) (f0 : NF) (hz : Cons Ax [neg f0])
include hC hz

theorem gam_list : ∀ L : List NF, (∀ x, x ∈ L → Gam Ax f0 x) →
    ∃ M, ∀ x, x ∈ L → x ∈ chain Ax f0 M
  | [], _ => ⟨0, fun _ hx => absurd hx List.not_mem_nil⟩
  | g :: L, hL => by
      obtain ⟨M, hM⟩ := gam_list L (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      obtain ⟨m, hm⟩ := hL g (List.mem_cons_self ..)
      refine ⟨max M m, fun x hx => ?_⟩
      cases List.mem_cons.mp hx with
      | inl he => subst he; exact chain_mono f0 (Nat.le_max_right M m) x hm
      | inr hx => exact chain_mono f0 (Nat.le_max_left M m) x (hM x hx)

theorem gam_consistent {L : List NF} (hL : ∀ x, x ∈ L → Gam Ax f0 x) :
    ¬ Der NF.imp (Thm Ax) L NF.bot := by
  intro d
  obtain ⟨M, hM⟩ := gam_list hC f0 hz L hL
  exact chain_cons hC f0 hz M (d.mono hM)

theorem gam_complete (g : NF) : Gam Ax f0 g ∨ Gam Ax f0 (neg g) := by
  let m := Cantor.toNat (code g, 0)
  have hm : enumF (Cantor.ofNat m).1 = g := by
    simp only [m, Cantor.ofNat_toNat, enumF_code]
  by_cases hc : Cons Ax (g :: chain Ax f0 m)
  · refine .inl ⟨m + 1, ?_⟩
    simp only [chain, step, hm, hc, if_true]
    exact List.mem_cons_self ..
  · refine .inr ⟨m + 1, ?_⟩
    simp only [chain, step, hm, hc, if_false]
    exact neg_mem_reject _ _ _

theorem gam_closed {L : List NF} {g : NF} (hL : ∀ x, x ∈ L → Gam Ax f0 x)
    (d : Der NF.imp (Thm Ax) L g) : Gam Ax f0 g :=
  (gam_complete hC f0 hz g).resolve_right fun h => gam_consistent hC f0 hz (L := neg g :: L)
    (List.forall_mem_cons.2 ⟨h, hL⟩) (.mp (.hyp (List.mem_cons_self ..)) d.weaken)

theorem gam_thm {g : NF} (h : Thm Ax g) : Gam Ax f0 g :=
  gam_closed hC f0 hz (L := []) (fun _ hx => absurd hx List.not_mem_nil) (.ax h)

theorem gam_mp {a b : NF} (hab : Gam Ax f0 (imp a b)) (ha : Gam Ax f0 a) : Gam Ax f0 b :=
  gam_closed hC f0 hz (L := [imp a b, a])
    (List.forall_mem_cons.2 ⟨hab,
      List.forall_mem_cons.2 ⟨ha, fun _ hx => absurd hx List.not_mem_nil⟩⟩)
    (.mp (.hyp (List.mem_cons_self ..)) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem gam_not_both {g : NF} (h1 : Gam Ax f0 g) (h2 : Gam Ax f0 (neg g)) : False :=
  gam_consistent hC f0 hz (L := [neg g, g])
    (List.forall_mem_cons.2 ⟨h2,
      List.forall_mem_cons.2 ⟨h1, fun _ hx => absurd hx List.not_mem_nil⟩⟩)
    (.mp (.hyp (List.mem_cons_self ..)) (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem gam_bot : ¬ Gam Ax f0 NF.bot := fun h =>
  gam_consistent hC f0 hz (L := [NF.bot])
    (List.forall_mem_cons.2 ⟨h, fun _ hx => absurd hx List.not_mem_nil⟩)
    (.hyp (List.mem_cons_self ..))

theorem gam_imp_iff (a b : NF) : Gam Ax f0 (imp a b) ↔ (Gam Ax f0 a → Gam Ax f0 b) := by
  refine ⟨gam_mp hC f0 hz, fun h => ?_⟩
  cases gam_complete hC f0 hz a with
  | inl ha => exact gam_mp hC f0 hz (gam_thm hC f0 hz (hC.k b a)) (h ha)
  | inr hna =>
      have t : Thm Ax (imp (neg a) (imp a b)) :=
        ded2 hC (.mp (.ax (hC.efq b)) (.mp h1 h0))
      exact gam_mp hC f0 hz (gam_thm hC f0 hz t) hna

/-- Every refuted universal formula has witnesses above every bound. -/
theorem gam_witness {a : Nat} {χ : NF} (hn : ¬ Gam Ax f0 (all a χ)) (hb : ¬ Bound a χ)
    (N : Nat) : ∃ c, N ≤ c ∧ c ≠ a ∧ ¬ Occurs c χ ∧ ¬ Gam Ax f0 (rn a c χ) := by
  let m := Cantor.toNat (code (all a χ), N)
  have hm : enumF (Cantor.ofNat m).1 = all a χ := by
    simp only [m, Cantor.ofNat_toNat, enumF_code]
  have hNm : N ≤ m := by
    have := Cantor.add_le_toNat (code (all a χ)) N
    omega
  have hc : ¬ Cons Ax (all a χ :: chain Ax f0 m) := by
    refine fun hc => hn ⟨m + 1, ?_⟩
    simp only [chain, step, hm, hc, if_true]
    exact List.mem_cons_self ..
  let c := max (topL (all a χ :: chain Ax f0 m)) m
  have htop : top (all a χ) ≤ c := by
    have := top_le_topL (g := all a χ) (G := all a χ :: chain Ax f0 m) (List.mem_cons_self ..)
    omega
  simp only [top] at htop
  refine ⟨c, by omega, by omega, not_occurs_of_top_le (by omega), fun hg =>
    gam_not_both hC f0 hz hg ⟨m + 1, ?_⟩⟩
  simp [chain, step, hm, hc, reject, hb]
  exact Or.inl rfl

/-- Every label has provably equal labels above every bound. -/
theorem gam_rich (j N : Nat) : ∃ c, N ≤ c ∧ Gam Ax f0 (NF.eq c j) := by
  let a := j + 1
  have hex : Gam Ax f0 (ex a (NF.eq a j)) := gam_thm hC f0 hz (.rho1 a j)
  have hn : ¬ Gam Ax f0 (all a (neg (NF.eq a j))) := fun h => gam_not_both hC f0 hz h hex
  have hb : ¬ Bound a (neg (NF.eq a j)) := by simp [neg, Bound]
  obtain ⟨c, hNc, hca, _, hc⟩ := gam_witness hC f0 hz hn hb N
  refine ⟨c, hNc, ?_⟩
  have hja : j ≠ a := by omega
  have hr : rn a c (neg (NF.eq a j)) = neg (NF.eq c j) := by
    simp [rn, neg, rv, hja]
  rw [hr] at hc
  exact (gam_complete hC f0 hz (NF.eq c j)).resolve_right hc

end Maximal

/-! ## The term model -/

section Model


def eqvSetoid (hC : Classical NF.imp NF.bot (Thm Ax)) (f0 : NF) (hz : Cons Ax [neg f0]) : Setoid Nat where
  r i j := Gam Ax f0 (NF.eq i j)
  iseqv := {
    refl := fun i => gam_thm hC f0 hz (eq_refl hC i)
    symm := fun h => gam_mp hC f0 hz (gam_thm hC f0 hz (eq_symm hC _ _)) h
    trans := fun h1 h2 =>
      gam_mp hC f0 hz (gam_mp hC f0 hz (gam_thm hC f0 hz (eq_trans hC _ _ _)) h1) h2 }

def Dom (hC : Classical NF.imp NF.bot (Thm Ax)) (f0 : NF) (hz : Cons Ax [neg f0]) : Type := Quotient (eqvSetoid hC f0 hz)

theorem rel_congr (hC : Classical NF.imp NF.bot (Thm Ax)) (f0 : NF) (hz : Cons Ax [neg f0]) {a1 b1 a2 b2 : Nat} (ha : Gam Ax f0 (NF.eq a1 a2))
    (hb : Gam Ax f0 (NF.eq b1 b2)) (h : Gam Ax f0 (rel a1 b1)) : Gam Ax f0 (rel a2 b2) :=
  gam_mp hC f0 hz (gam_mp hC f0 hz (gam_thm hC f0 hz (.rho3 b1 b2 a2)) hb)
    (gam_mp hC f0 hz (gam_mp hC f0 hz (gam_thm hC f0 hz (.rho5 a2 b1 a1)) ha) h)

def memD (hC : Classical NF.imp NF.bot (Thm Ax)) (f0 : NF) (hz : Cons Ax [neg f0]) : Dom hC f0 hz → Dom hC f0 hz → Prop :=
  Quotient.lift₂ (s₁ := eqvSetoid hC f0 hz) (s₂ := eqvSetoid hC f0 hz)
    (fun i j => Gam Ax f0 (rel i j))
    (fun a1 b1 a2 b2 ha hb => propext ⟨rel_congr hC f0 hz ha hb,
      rel_congr hC f0 hz ((eqvSetoid hC f0 hz).iseqv.symm ha)
        ((eqvSetoid hC f0 hz).iseqv.symm hb)⟩)

def e0 (hC : Classical NF.imp NF.bot (Thm Ax)) (f0 : NF) (hz : Cons Ax [neg f0]) : Nat → Dom hC f0 hz := fun i => Quotient.mk (eqvSetoid hC f0 hz) i

theorem truth (hC : Classical NF.imp NF.bot (Thm Ax)) (f0 : NF) (hz : Cons Ax [neg f0]) : ∀ n (f : NF), size f < n → Clean f →
    (Sat (memD hC f0 hz) (e0 hC f0 hz) f ↔ Gam Ax f0 f)
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, rel i j, _, _ => Iff.rfl
  | n + 1, NF.eq i j, _, _ => by
      simp only [Sat, e0]
      exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  | n + 1, NF.bot, _, _ => ⟨False.elim, gam_bot hC f0 hz⟩
  | n + 1, imp a b, hs, hcl => by
      simp only [size] at hs
      simp only [Sat]
      rw [truth hC f0 hz n a (by omega) hcl.1, truth hC f0 hz n b (by omega) hcl.2,
        gam_imp_iff hC f0 hz]
  | n + 1, all a χ, hs, hcl => by
      simp only [size] at hs
      obtain ⟨hb, hcχ⟩ := hcl
      simp only [Sat]
      refine ⟨fun hsat => Classical.byContradiction fun hn => ?_, fun hg d => ?_⟩
      · obtain ⟨c, _, hca, hco, hg⟩ := gam_witness hC f0 hz hn hb 0
        apply hg
        have hcb : ¬ Bound c χ := fun b => hco (bound_occurs b)
        rw [← truth hC f0 hz n (rn a c χ) (by rw [size_rn]; omega) (clean_rn a c χ hcχ),
          sat_rn _ a c χ _ hb hcb]
        exact hsat _
      · induction d using Quotient.inductionOn with
        | h j =>
          obtain ⟨c, hNc, hcj⟩ := gam_rich hC f0 hz j (top (all a χ))
          simp only [top] at hNc
          have hca : c ≠ a := by omega
          have hcb : ¬ Bound c χ := fun b => not_occurs_of_top_le (by omega) (bound_occurs b)
          have hd : (Quotient.mk (eqvSetoid hC f0 hz) j : Dom hC f0 hz) = e0 hC f0 hz c :=
            Quotient.sound ((eqvSetoid hC f0 hz).iseqv.symm hcj)
          rw [hd, ← sat_rn _ a c χ _ hb hcb,
            truth hC f0 hz n (rn a c χ) (by rw [size_rn]; omega) (clean_rn a c χ hcχ)]
          exact gam_mp hC f0 hz (gam_thm hC f0 hz (spec hC hca hb hcb)) hg

end Model

/-! ## Closures and the completeness theorem -/

/-- Universal closure over the labels `0, …, n-1`. -/
def close : Nat → NF → NF
  | 0, g => g
  | n + 1, g => close n (all n g)

theorem thm_close {B : NF → Prop} : ∀ (n : Nat) {g : NF}, Thm B g → Thm B (close n g)
  | 0, _, h => h
  | n + 1, _, h => thm_close n (.gen n h)

theorem sat_close {V : Type} (mem : V → V → Prop) :
    ∀ (n : Nat) (g : NF) (e : Nat → V), Sat mem e (close n g) →
      ∀ e' : Nat → V, (∀ k, n ≤ k → e' k = e k) → Sat mem e' g
  | 0, g, e, h, e', he' => by
      have : e' = e := funext fun k => he' k (Nat.zero_le k)
      subst this; exact h
  | n + 1, g, e, h, e', he' => by
      have h1 := sat_close mem n (all n g) e h (update e' n (e n)) (by
        intro k hk
        by_cases hkn : k = n
        · subst hkn; simp [update]
        · simp only [update, hkn, if_false]; exact he' k (by omega))
      have h2 := h1 (e' n)
      have : update (update e' n (e n)) n (e' n) = e' := by
        funext k; by_cases hk : k = n <;> simp [update, hk]
      rwa [this] at h2

theorem free_lt_top {n : Nat} {g : NF} (h : NF.Free n g) : n < top g :=
  occurs_lt_top (NF.Free.occurs h)

/-- Completeness of the machine rows for first-order consequence. -/
theorem completeness (hC : Classical NF.imp NF.bot (Thm Ax))
    (hC0 : Classical NF.imp NF.bot (Thm (fun _ => False))) (f : NF)
    (hval : ∀ (D : Type) (mem : D → D → Prop),
      (∀ a, Ax a → ∀ e : Nat → D, Sat mem e a) → ∀ e : Nat → D, Sat mem e f) :
    Thm Ax f := by
  refine Classical.byContradiction fun hnot => ?_
  -- The clean form of the target.
  have hE : ∀ (K : Nat) (g : NF), top g ≤ K →
      Thm (fun _ => False) (imp g (cl K 0 g)) ∧ Thm (fun _ => False) (imp (cl K 0 g) g) :=
    fun K g h => cl_equiv hC0 K 0 g h
  have semE : ∀ (K : Nat) (g : NF), top g ≤ K → ∀ {D : Type} (mem : D → D → Prop) (e : Nat → D),
      Sat mem e g ↔ Sat mem e (cl K 0 g) := by
    intro K g h D mem e
    exact ⟨soundness (mem := mem) (Ax := fun _ => False) (fun _ h => h.elim) (hE K g h).1 e,
      soundness (mem := mem) (Ax := fun _ => False) (fun _ h => h.elim) (hE K g h).2 e⟩
  let f0 := cl (top f) 0 f
  have hz : Cons Ax [neg f0] := by
    intro d
    apply hnot
    exact hC.mp (Thm.mono (fun _ h => h.elim) (hE (top f) f (Nat.le_refl _)).2)
      (hC.mp (dne hC f0) (thm_of_der0 hC (deduction hC d)))
  -- The model satisfies the theory.
  have hAx : ∀ a, Ax a → ∀ e : Nat → Dom hC f0 hz, Sat (memD hC f0 hz) e a := by
    intro a ha e
    let g := close (top a) a
    have hclean : Clean (cl (top g) 0 g) := clean_cl _ 0 g
    have hg : Gam Ax f0 (cl (top g) 0 g) :=
      gam_thm hC f0 hz (hC.mp (Thm.mono (fun _ h => h.elim) (hE (top g) g (Nat.le_refl _)).1)
        (thm_close _ (.ax ha)))
    have hs := (truth hC f0 hz (size (cl (top g) 0 g) + 1) _ (Nat.lt_succ_self _) hclean).mpr hg
    rw [← semE (top g) g (Nat.le_refl _)] at hs
    let e' : Nat → Dom hC f0 hz := fun k => if k < top a then e k else e0 hC f0 hz k
    have h1 := sat_close (memD hC f0 hz) (top a) a (e0 hC f0 hz) hs e' (by
      intro k hk; simp only [e']; simp [Nat.not_lt.mpr hk])
    refine (sat_ext (memD hC f0 hz) a e e' fun n hn => ?_).mpr h1
    simp only [e', free_lt_top hn, if_true]
  have hf := hval (Dom hC f0 hz) (memD hC f0 hz) hAx (e0 hC f0 hz)
  rw [semE (top f) f (Nat.le_refl _)] at hf
  have hin := (truth hC f0 hz (size f0 + 1) f0 (Nat.lt_succ_self _) (clean_cl _ 0 f)).mp hf
  exact gam_not_both hC f0 hz hin ⟨0, List.mem_cons_self ..⟩

end SetTheory.BusyBeaver.ZFC.Tarski
