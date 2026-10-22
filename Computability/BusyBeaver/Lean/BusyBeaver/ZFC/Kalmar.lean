/-!
Classical implicational completeness for an arbitrary theorem predicate.

Let `T : α → Prop` be closed under modus ponens for a binary operation
`imp : α → α → α` and contain every instance of K, S, Peirce's law and
ex falso for a designated element `bot`. Then `T` contains every instance of
every classical tautology built from propositional variables, `⊥` and `→`.

This is the propositional half of the logic bridge of every proof calculus
considered for the ZFC machine: `Lukasiewicz.lean` derives K, S and Peirce from
the single row `rho8`, and ex falso comes from the calculus's falsity row.
Nothing about `imp` is assumed: it need not be injective, and numerical code
aliases such as `imp 0 0 = 0` are harmless.

The proof is Kalmár's: a deduction theorem for derivations from finite
hypothesis lists, the truth-table lemma for literal hypotheses, and
elimination of one hypothesis at a time by the classical case split
`(p → φ) → ((¬p → φ) → φ)`, itself derived from Peirce's law.
-/

namespace SetTheory.BusyBeaver.ZFC.Kalmar

universe u
variable {α : Type u}

/-- A theorem predicate with the classical implicational axioms. -/
structure Classical (imp : α → α → α) (bot : α) (T : α → Prop) : Prop where
  mp : ∀ {a b : α}, T (imp a b) → T a → T b
  k : ∀ a b : α, T (imp a (imp b a))
  s : ∀ a b c : α, T (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  peirce : ∀ a b : α, T (imp (imp (imp a b) a) a)
  efq : ∀ a : α, T (imp bot a)

/-- Derivations from a finite list of hypotheses. -/
inductive Der (imp : α → α → α) (T : α → Prop) : List α → α → Prop
  | ax {G : List α} {a : α} : T a → Der imp T G a
  | hyp {G : List α} {a : α} : a ∈ G → Der imp T G a
  | mp {G : List α} {a b : α} : Der imp T G (imp a b) → Der imp T G a → Der imp T G b

section Deduction

variable {imp : α → α → α} {bot : α} {T : α → Prop}

theorem Der.mono {G : List α} {a : α} (d : Der imp T G a) {G' : List α}
    (hsub : ∀ x, x ∈ G → x ∈ G') : Der imp T G' a := by
  induction d with
  | ax h => exact .ax h
  | hyp h => exact .hyp (hsub _ h)
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2

theorem Der.sound {G : List α} {a : α} (h : Classical imp bot T) (d : Der imp T G a)
    (hG : ∀ x, x ∈ G → T x) : T a := by
  induction d with
  | ax ha => exact ha
  | hyp hm => exact hG _ hm
  | mp _ _ ih1 ih2 => exact h.mp ih1 ih2

theorem self_imp (h : Classical imp bot T) (a : α) : T (imp a a) :=
  h.mp (h.mp (h.s a (imp a a) a) (h.k a (imp a a))) (h.k a a)

theorem deduction_aux (h : Classical imp bot T) {a : α} {G' : List α} {b : α}
    (d : Der imp T G' b) : ∀ G : List α, G' = a :: G → Der imp T G (imp a b) := by
  induction d with
  | ax hb => exact fun G _ => .mp (.ax (h.k _ a)) (.ax hb)
  | hyp hm =>
      rintro G rfl
      rcases List.mem_cons.mp hm with rfl | hin
      · exact .ax (self_imp h _)
      · exact .mp (.ax (h.k _ a)) (.hyp hin)
  | mp _ _ ih1 ih2 => exact fun G hG => .mp (.mp (.ax (h.s _ _ _)) (ih1 G hG)) (ih2 G hG)

/-- The deduction theorem. -/
theorem deduction (h : Classical imp bot T) {G : List α} {a b : α}
    (d : Der imp T (a :: G) b) : Der imp T G (imp a b) :=
  deduction_aux h d G rfl

theorem Der.cons_head {G : List α} {a : α} : Der imp T (a :: G) a :=
  .hyp (List.mem_cons_self ..)

theorem Der.weaken {G : List α} {a b : α} (d : Der imp T G b) : Der imp T (a :: G) b :=
  d.mono (fun _ hx => List.mem_cons_of_mem _ hx)

/-- Classical case split on `p`. -/
theorem cases_on (h : Classical imp bot T) {G : List α} {p c : α}
    (d1 : Der imp T (p :: G) c) (d0 : Der imp T (imp p bot :: G) c) : Der imp T G c := by
  -- Under `c → ⊥`, the first branch refutes `p`, and the second then gives `c`.
  have hp : Der imp T G (imp p c) := deduction h d1
  have hn : Der imp T G (imp (imp p bot) c) := deduction h d0
  have inner : Der imp T (imp c bot :: G) c := by
    have notp : Der imp T (imp c bot :: G) (imp p bot) :=
      deduction h (.mp (.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        (.mp hp.weaken.weaken .cons_head))
    exact .mp hn.weaken notp
  exact .mp (.ax (h.peirce c bot)) (deduction h inner)

end Deduction

/-! ## Propositional formulas and Kalmár's lemma -/

inductive PF : Type
  | var : Nat → PF
  | bot : PF
  | imp : PF → PF → PF
  deriving DecidableEq

namespace PF

def eval (imp : α → α → α) (bot : α) (σ : Nat → α) : PF → α
  | var n => σ n
  | PF.bot => bot
  | PF.imp a b => imp (eval imp bot σ a) (eval imp bot σ b)

def truth (v : Nat → Bool) : PF → Bool
  | var n => v n
  | PF.bot => false
  | PF.imp a b => !truth v a || truth v b

/-- Every variable of the formula is below `n`. -/
def Bounded (n : Nat) : PF → Prop
  | var m => m < n
  | PF.bot => True
  | PF.imp a b => Bounded n a ∧ Bounded n b

def Tautology (f : PF) : Prop := ∀ v : Nat → Bool, truth v f = true

end PF

section Kalmar

variable {imp : α → α → α} {bot : α} {T : α → Prop}

/-- The literal of an element under a truth value. -/
def lit (imp : α → α → α) (bot : α) (b : Bool) (x : α) : α :=
  if b then x else imp x bot

/-- Literal hypotheses for the variables `0, …, n-1`. -/
def hyps (imp : α → α → α) (bot : α) (σ : Nat → α) (v : Nat → Bool) : Nat → List α
  | 0 => []
  | n + 1 => lit imp bot (v n) (σ n) :: hyps imp bot σ v n

theorem lit_mem_hyps (σ : Nat → α) (v : Nat → Bool) :
    ∀ {n m : Nat}, m < n → lit imp bot (v m) (σ m) ∈ hyps imp bot σ v n
  | 0, _, hm => absurd hm (Nat.not_lt_zero _)
  | n + 1, m, hm => by
      by_cases he : m = n
      · subst he; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (lit_mem_hyps σ v (by omega))

theorem hyps_congr (σ : Nat → α) (v w : Nat → Bool) :
    ∀ n, (∀ m, m < n → v m = w m) → hyps imp bot σ v n = hyps imp bot σ w n
  | 0, _ => rfl
  | n + 1, hvw => by
      simp only [hyps]
      rw [hvw n (by omega), hyps_congr σ v w n (fun m hm => hvw m (by omega))]

/-- Kalmár's lemma: the literal of every bounded formula is derivable. -/
theorem kalmar (h : Classical imp bot T) (σ : Nat → α) (v : Nat → Bool) (n : Nat) :
    ∀ f : PF, PF.Bounded n f →
      Der imp T (hyps imp bot σ v n) (lit imp bot (PF.truth v f) (PF.eval imp bot σ f))
  | .var m, hb => .hyp (lit_mem_hyps σ v hb)
  | .bot, _ => by
      simp only [PF.truth, PF.eval, lit]
      exact .ax (self_imp h bot)
  | .imp a b, hb => by
      have da := kalmar h σ v n a hb.1
      have db := kalmar h σ v n b hb.2
      cases hta : PF.truth v a <;> cases htb : PF.truth v b <;>
        simp only [hta, htb, lit, PF.truth, PF.eval, Bool.not_false, Bool.not_true,
          Bool.true_or, Bool.false_or, if_true] at da db ⊢
      · -- a false: from ¬a derive a → b through ex falso.
        exact deduction h (.mp (.ax (h.efq _)) (.mp da.weaken .cons_head))
      · exact .mp (.ax (h.k _ _)) db
      · -- a true, b false: refute a → b.
        exact deduction h (.mp db.weaken (.mp .cons_head da.weaken))
      · exact .mp (.ax (h.k _ _)) db

/-- Elimination of the literal hypotheses, one variable at a time. -/
theorem eliminate (h : Classical imp bot T) (σ : Nat → α) (c : α) :
    ∀ n, (∀ v : Nat → Bool, Der imp T (hyps imp bot σ v n) c) → Der imp T [] c
  | 0, hall => hall (fun _ => false)
  | n + 1, hall => by
      refine eliminate h σ c n fun v => ?_
      have h1 := hall (fun m => if m = n then true else v m)
      have h0 := hall (fun m => if m = n then false else v m)
      simp only [hyps] at h1 h0
      rw [hyps_congr σ _ v n (fun m hm => by simp [Nat.ne_of_lt hm])] at h1 h0
      exact cases_on h h1 h0

/-- Classical completeness: every tautology instance is a theorem. -/
theorem tautology_complete (h : Classical imp bot T) (f : PF) (n : Nat)
    (hb : PF.Bounded n f) (ht : PF.Tautology f) (σ : Nat → α) :
    T (PF.eval imp bot σ f) := by
  have d : Der imp T [] (PF.eval imp bot σ f) := by
    refine eliminate h σ _ n fun v => ?_
    simpa only [ht v, lit, if_true] using kalmar h σ v n f hb
  exact d.sound h (fun _ hx => absurd hx (List.not_mem_nil))

end Kalmar

end SetTheory.BusyBeaver.ZFC.Kalmar
