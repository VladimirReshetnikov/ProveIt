import Mathlib.Computability.Primrec.Basic
import Mathlib.Tactic.FunProp

/-!
Compositional automation for the extensional `Primrec` proofs in
`DiophantineConsistency/Computability.lean`, snapshot e73fa2e916c9.
The original pairing P is left parametric; `hP : Primrec₂ P` is exactly
what upstream `pr_P` already proves. No executable code is changed.
-/
namespace PrimrecFunProp

attribute [local fun_prop] Primrec
attribute [local fun_prop] Primrec.id Primrec.const Primrec.comp
  Primrec.fst Primrec.snd Primrec.pair

@[local fun_prop] theorem add_rule {α} [Primcodable α] {f g : α → Nat}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => f x + g x) :=
  Primrec.nat_add.comp hf hg

@[local fun_prop] theorem mul_rule {α} [Primcodable α] {f g : α → Nat}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => f x * g x) :=
  Primrec.nat_mul.comp hf hg

section Pairing
variable (P : Nat → Nat → Nat)

def wim (a b : Nat) : Nat := 4 * P a b
def wel (i j : Nat) : Nat := 4 * P i j + 1
def wal (i a : Nat) : Nat := 4 * P i a + 2
def weq (i j : Nat) : Nat := 4 * P i j + 3
def wn (a : Nat) : Nat := wim P a 1
def wex (x a : Nat) : Nat := wn P (wal P x (wn P a))
def rho8 (a b c u : Nat) : Nat :=
  wim P (wim P (wim P c u) a) (wim P (wim P a c) (wim P b c))
def rho6 (a b : Nat) : Nat := wim P (wex P a (wal P a b)) b
def rho5 (a b c : Nat) : Nat := wim P (weq P c a) (wim P (wel P c b) (wel P a b))
def rho4 (a b c : Nat) : Nat := wim P (wal P a (wal P b c)) (wal P b (wal P a c))
def rho3 (a b c : Nat) : Nat := wim P (weq P a b) (wim P (wel P c a) (wel P c b))
def rho2 (a b c : Nat) : Nat := wim P (wal P a (wim P b c)) (wim P (wal P a b) (wal P a c))
def rho1 (a b : Nat) : Nat := wex P a (weq P a b)
def growG (a b c : Nat) : Nat :=
  wim P (weq P c a) (wim P (weq P c b) (wal P (wel P a b) (weq P a b)))
def req (b k m : Nat) : Nat :=
  wal P b (wim P m (wn P (wal P b (wim P m (wn P (wel P b k))))))
def clos (a b k m : Nat) : Nat :=
  wal P b (wim P (wel P b k) (wn P (wal P a (wim P m
    (wn P (wal P a (wim P (wal P k (wim P (wel P k a) (wel P k b)))
      (req P b k m))))))))
def axStack (a h b c u t w : Nat) : Nat :=
  P (rho1 P a b) (P (rho2 P a b c) (P (rho3 P a b c) (P (rho4 P a b c)
    (P (rho5 P a b c) (P (rho6 P a c) (P (growG P a b c)
      (P (rho8 P a b c u) (P (wal P u h) (P t w)))))))))
end Pairing

section Rules
variable {P : Nat → Nat → Nat} (hP : Primrec₂ P)
variable {α : Type} [Primcodable α] {a b c d : α → Nat}
include hP

@[local fun_prop] theorem wim_rule (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun v => wim P (a v) (b v)) :=
  Primrec.nat_mul.comp (Primrec.const 4) (hP.comp ha hb)

@[local fun_prop] theorem wel_rule (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun v => wel P (a v) (b v)) :=
  Primrec.nat_add.comp (wim_rule hP ha hb) (Primrec.const 1)

@[local fun_prop] theorem wal_rule (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun v => wal P (a v) (b v)) :=
  Primrec.nat_add.comp (wim_rule hP ha hb) (Primrec.const 2)

@[local fun_prop] theorem weq_rule (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun v => weq P (a v) (b v)) :=
  Primrec.nat_add.comp (wim_rule hP ha hb) (Primrec.const 3)

@[local fun_prop] theorem wn_rule (ha : Primrec a) :
    Primrec (fun v => wn P (a v)) := by
  unfold wn
  fun_prop (disch := assumption)

@[local fun_prop] theorem wex_rule (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun v => wex P (a v) (b v)) := by
  unfold wex
  fun_prop (disch := assumption)

@[local fun_prop] theorem rho1_rule (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun v => rho1 P (a v) (b v)) := by
  unfold rho1
  fun_prop (disch := assumption)

@[local fun_prop] theorem rho2_rule (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec (fun v => rho2 P (a v) (b v) (c v)) := by
  unfold rho2
  fun_prop (disch := assumption)

@[local fun_prop] theorem rho3_rule (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec (fun v => rho3 P (a v) (b v) (c v)) := by
  unfold rho3
  fun_prop (disch := assumption)

@[local fun_prop] theorem rho4_rule (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec (fun v => rho4 P (a v) (b v) (c v)) := by
  unfold rho4
  fun_prop (disch := assumption)

@[local fun_prop] theorem rho5_rule (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec (fun v => rho5 P (a v) (b v) (c v)) := by
  unfold rho5
  fun_prop (disch := assumption)

@[local fun_prop] theorem rho6_rule (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun v => rho6 P (a v) (b v)) := by
  unfold rho6
  fun_prop (disch := assumption)

@[local fun_prop] theorem rho8_rule (ha : Primrec a) (hb : Primrec b)
    (hc : Primrec c) (hd : Primrec d) :
    Primrec (fun v => rho8 P (a v) (b v) (c v) (d v)) := by
  unfold rho8
  fun_prop (disch := assumption)

@[local fun_prop] theorem growG_rule (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec (fun v => growG P (a v) (b v) (c v)) := by
  unfold growG
  fun_prop (disch := assumption)

@[local fun_prop] theorem req_rule (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec (fun v => req P (a v) (b v) (c v)) := by
  unfold req
  fun_prop (disch := assumption)

@[local fun_prop] theorem clos_rule (ha : Primrec a) (hb : Primrec b)
    (hc : Primrec c) (hd : Primrec d) :
    Primrec (fun v => clos P (a v) (b v) (c v) (d v)) := by
  unfold clos
  fun_prop (disch := assumption)

theorem axStack_rule {u t w : α → Nat} (ha : Primrec a) (hb : Primrec b)
    (hc : Primrec c) (hd : Primrec d) (hu : Primrec u) (ht : Primrec t) (hw : Primrec w) :
    Primrec (fun v => axStack P (a v) (b v) (c v) (d v) (u v) (t v) (w v)) := by
  change Primrec (fun p : Nat × Nat => P p.1 p.2) at hP
  unfold axStack
  fun_prop (disch := assumption)

/-- A mixed product-domain example, avoiding six nested projection proofs. -/
theorem product_example :
    Primrec (fun v : Nat × Nat × Nat => rho2 P v.1 v.2.1 v.2.2) := by
  fun_prop (disch := assumption)

end Rules

#print axioms rho2_rule
#print axioms clos_rule
#print axioms axStack_rule
#print axioms product_example
end PrimrecFunProp
