/-!
The substitution-free Tarski calculus used by the ZFC machines.

Every calibrated ZFC proof search in this project — Mira-Cult's 254-state
machine and all complete-logic controls of the closure-kernel reports — keeps
the same eight logical rows. Written over named variables, with a genuine
falsity `bot` and an arbitrary set `Ax` of theory formulas, they are:

| row | formula |
|---|---|
| rho8 | `((c → u) → a) → ((a → c) → (b → c))` (Lukasiewicz) |
| rho2 | `∀a (b → c) → (∀a b → ∀a c)` |
| rho4 | `∀a ∀b c → ∀b ∀a c` |
| rho6 | `∃a ∀a b → b` |
| rho1 | `∃a (a = b)` |
| rho7 | `c = a → (c = b → a = b)` |
| rho5 | `c = a → (c ∈ b → a ∈ b)` |
| rho3 | `a = b → (c ∈ a → c ∈ b)` |
| vacuity | `R(a,b) → ∀c R(a,b)` for atoms, gated by `c ≠ a, b` |

together with modus ponens and generalization. No row performs syntactic
substitution: this is the Kalish–Montague restriction of Tarski's 1965
system, with vacuity only for atoms and the extra commutation and `rho6`
rows. This module fixes the syntax, the standard semantics and the calculus,
and proves soundness. The machine's numerical codes, its relative falsity
alias and its theory bundle are separate layers.
-/

namespace SetTheory.BusyBeaver.ZFC.Tarski

/-- Named first-order formulas over membership and equality. -/
inductive NF : Type
  | rel : Nat → Nat → NF
  | eq : Nat → Nat → NF
  | bot : NF
  | imp : NF → NF → NF
  | all : Nat → NF → NF
  deriving DecidableEq, Repr

namespace NF

def neg (a : NF) : NF := imp a bot

/-- Existential quantifier, `¬∀¬`. -/
def ex (i : Nat) (a : NF) : NF := neg (all i (neg a))

/-- The Lukasiewicz row `rho8` in the machine's parameter order `c u a b`. -/
def luk (c u a b : NF) : NF := imp (imp (imp c u) a) (imp (imp a c) (imp b c))

/-- Some occurrence of a label, bound or free. -/
def Occurs (n : Nat) : NF → Prop
  | rel i j => n = i ∨ n = j
  | eq i j => n = i ∨ n = j
  | bot => False
  | imp a b => Occurs n a ∨ Occurs n b
  | all i a => n = i ∨ Occurs n a

def Free (n : Nat) : NF → Prop
  | rel i j => n = i ∨ n = j
  | eq i j => n = i ∨ n = j
  | bot => False
  | imp a b => Free n a ∨ Free n b
  | all i a => n ≠ i ∧ Free n a

theorem Free.occurs {n : Nat} : ∀ {f : NF}, Free n f → Occurs n f
  | rel _ _, h => h
  | eq _ _, h => h
  | bot, h => h
  | imp _ _, h => h.elim (fun h => Or.inl (Free.occurs h)) (fun h => Or.inr (Free.occurs h))
  | all _ _, h => Or.inr (Free.occurs h.2)

end NF

open NF

/-! ## Semantics -/

universe u
variable {V : Type u}

def update (e : Nat → V) (i : Nat) (d : V) : Nat → V :=
  fun n => if n = i then d else e n

theorem update_same (e : Nat → V) (i : Nat) (d : V) : update e i d i = d := by
  simp [update]

theorem update_other (e : Nat → V) {i n : Nat} (d : V) (h : n ≠ i) : update e i d n = e n := by
  simp [update, h]

/-- Tarski satisfaction in a structure with equality interpreted as identity. -/
def Sat (mem : V → V → Prop) : (Nat → V) → NF → Prop
  | e, rel i j => mem (e i) (e j)
  | e, NF.eq i j => e i = e j
  | _, bot => False
  | e, imp a b => Sat mem e a → Sat mem e b
  | e, all i a => ∀ d, Sat mem (update e i d) a

theorem sat_ext (mem : V → V → Prop) :
    ∀ (f : NF) (e e' : Nat → V), (∀ n, Free n f → e n = e' n) →
      (Sat mem e f ↔ Sat mem e' f)
  | rel i j, e, e', h => by
      simp only [Sat]; rw [h i (Or.inl rfl), h j (Or.inr rfl)]
  | NF.eq i j, e, e', h => by
      simp only [Sat]; rw [h i (Or.inl rfl), h j (Or.inr rfl)]
  | bot, _, _, _ => Iff.rfl
  | imp a b, e, e', h => by
      simp only [Sat]
      rw [sat_ext mem a e e' (fun n hn => h n (Or.inl hn)),
        sat_ext mem b e e' (fun n hn => h n (Or.inr hn))]
  | all i a, e, e', h => by
      simp only [Sat]
      refine forall_congr' fun d => sat_ext mem a _ _ fun n hn => ?_
      by_cases hni : n = i
      · subst hni; simp [update]
      · simp only [update, hni, if_false]; exact h n ⟨hni, hn⟩

theorem sat_ex (mem : V → V → Prop) (e : Nat → V) (i : Nat) (a : NF) :
    Sat mem e (ex i a) ↔ ∃ d, Sat mem (update e i d) a := by
  simp only [ex, neg, Sat]
  exact ⟨fun h => Classical.byContradiction fun hn => h fun d hd => hn ⟨d, hd⟩,
    fun ⟨d, hd⟩ h => h d hd⟩

/-! ## The calculus -/

/-- Theorems of the machine's logical rows over a theory `Ax`. -/
inductive Thm (Ax : NF → Prop) : NF → Prop
  | ax {a : NF} : Ax a → Thm Ax a
  | mp {a b : NF} : Thm Ax (imp a b) → Thm Ax a → Thm Ax b
  | gen (i : Nat) {a : NF} : Thm Ax a → Thm Ax (all i a)
  | rho8 (c u a b : NF) : Thm Ax (luk c u a b)
  | rho2 (i : Nat) (b c : NF) : Thm Ax (imp (all i (imp b c)) (imp (all i b) (all i c)))
  | rho4 (i j : Nat) (c : NF) : Thm Ax (imp (all i (all j c)) (all j (all i c)))
  | rho6 (i : Nat) (b : NF) : Thm Ax (imp (ex i (all i b)) b)
  | rho1 (i j : Nat) : Thm Ax (ex i (NF.eq i j))
  | rho7 (a b c : Nat) : Thm Ax (imp (NF.eq c a) (imp (NF.eq c b) (NF.eq a b)))
  | rho5 (a b c : Nat) : Thm Ax (imp (NF.eq c a) (imp (rel c b) (rel a b)))
  | rho3 (a b c : Nat) : Thm Ax (imp (NF.eq a b) (imp (rel c a) (rel c b)))
  | vacRel (a b c : Nat) : c ≠ a → c ≠ b → Thm Ax (imp (rel a b) (all c (rel a b)))
  | vacEq (a b c : Nat) : c ≠ a → c ≠ b → Thm Ax (imp (NF.eq a b) (all c (NF.eq a b)))

/-- Soundness: every theorem holds in every model of the theory, under every
assignment. The domain is nonempty because an assignment exists. -/
theorem soundness {Ax : NF → Prop} {mem : V → V → Prop}
    (hAx : ∀ a, Ax a → ∀ e : Nat → V, Sat mem e a) :
    ∀ {f : NF}, Thm Ax f → ∀ e : Nat → V, Sat mem e f := by
  intro f hf
  induction hf with
  | ax h => exact hAx _ h
  | mp _ _ ih1 ih2 => exact fun e => ih1 e (ih2 e)
  | gen i _ ih => exact fun e d => ih _
  | rho8 c u a b =>
      exact fun e h1 h2 _ =>
        Classical.byContradiction fun hnc => hnc (h2 (h1 fun hc => absurd hc hnc))
  | rho2 i b c => exact fun e h1 h2 d => h1 d (h2 d)
  | rho4 i j c =>
      intro e h dj di
      by_cases hij : i = j
      · subst hij; exact h dj di
      · have hh : update (update e i di) j dj = update (update e j dj) i di := by
          funext n
          simp only [update]
          by_cases hn : n = i <;> by_cases hm : n = j
          · exact absurd (hn.symm.trans hm) hij
          · simp [hn, hij]
          · simp [hm, Ne.symm hij]
          · simp [hn, hm]
        rw [← hh]; exact h di dj
  | rho6 i b =>
      intro e h
      obtain ⟨d, hd⟩ := (sat_ex mem e i _).mp h
      have := hd (e i)
      have hh : update (update e i d) i (e i) = e := by
        funext n; by_cases hn : n = i <;> simp [update, hn]
      rwa [hh] at this
  | rho1 i j =>
      intro e
      rw [sat_ex]
      refine ⟨e j, ?_⟩
      by_cases hij : j = i
      · subst hij; simp [Sat, update]
      · simp [Sat, update, hij]
  | rho7 a b c =>
      intro e h1 h2
      simp only [Sat] at h1 h2 ⊢
      rw [← h1, ← h2]
  | rho5 a b c | rho3 a b c =>
      intro e h1 h2
      simp only [Sat] at h1 h2 ⊢
      rwa [← h1]
  | vacRel a b c hca hcb | vacEq a b c hca hcb =>
      intro e h d
      simp only [Sat, update, if_neg (Ne.symm hca), if_neg (Ne.symm hcb)]
      exact h

end SetTheory.BusyBeaver.ZFC.Tarski
