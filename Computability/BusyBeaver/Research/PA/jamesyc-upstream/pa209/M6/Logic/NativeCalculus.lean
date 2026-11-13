module
public import M6.Source.Cantor
@[expose] public section

/-! Literal numeric formula constructors and the dominated-rho8 proof calculus.
Constructors/bundle transcribe PA/m238/coq/logic/Codes238.v at upstream commit
84049b5e753190cf328cbc2d2710791ad32ad59c. Rules follow Compiler238.v:186–198,
with the explicit `u ≤ a` restriction required by the reconstructed PA135 source.
This is NOT Foundation PA; calibration and numeric readback remain separate.
The M6 row list below uses the changed rho6(A,B) head and retains wal(U,h).
This is not the original contextual209 rho6(A,c) row list. -/
namespace M6.PA.NativeCalculus
open M6.Source.Cantor

@[irreducible] def wim := implication
@[irreducible] def wal := universal
def wel (a b : Nat) := 4 * pair a b + 1
def weq (a b : Nat) := 4 * pair a b + 3
def wn (a : Nat) := wim a 1
def wa (a b : Nat) := wn (wim a (wn b))
def wex (a b : Nat) := wn (wal a (wn b))

def rho1 a b := wex a (weq a b)
def rho2 a b c := wim (wal a (wim b c)) (wim (wal a b) (wal a c))
def rho3 a b c := wim (wel a b) (wim (weq b c) (wel a c))
def rho4 a b c := wim (wal a (wal b c)) (wal b (wal a c))
def rho5 a b c := wim (weq a b) (wim (wel a c) (wel b c))
def rho6 a b := wim (wex a (wal a b)) b
def rho7 a b c := wim (weq a b) (wim (weq a c) (weq b c))
def rho8 a b c u := wim (wim (wim c u) a) (wim (wim a c) (wim b c))

def bundle a b c :=
  wa (wex c
        (wa (wal b (wa (wim (wel a b) (wim c (wel c b)))
                        (wim (wel c b) c)))
            (wim c (wel c b))))
     (wa (wim (weq a b) (wal c (weq a b)))
         (wim (wel a b) (wal c (wel a b))))

def gate (a b c : Nat) := if c = a ∨ c = b then 0 else bundle a b c

set_option maxHeartbeats 1000000 in
/-- Actual finite proof trees, rather than an opaque theorem predicate. -/
inductive Derivation : Nat → Type where
  | truth : Derivation 0
  | mp {a b} : Derivation a → Derivation (wim a b) → Derivation b
  | all (a) {b} : Derivation b → Derivation (wal a b)
  | r1 (a b) : Derivation (rho1 a b)
  | r2 (a b c) : Derivation (rho2 a b c)
  | r3 (a b c) : Derivation (rho3 a b c)
  | r4 (a b c) : Derivation (rho4 a b c)
  | r5 (a b c) : Derivation (rho5 a b c)
  | r6 (a b) : Derivation (rho6 a b)
  | r7 (a b c) : Derivation (rho7 a b c)
  | r8 (a b c u) : u ≤ a → Derivation (rho8 a b c u)
  | guardedBundle (a b c) : c ≠ a → c ≠ b → Derivation (bundle a b c)

def Proved (x : Nat) : Prop := Nonempty (Derivation x)

def Derivation.size {x} : Derivation x → Nat
  | .mp p q => p.size + q.size + 1
  | .all _ p => p.size + 1
  | _ => 1

/-- Exact nine new PA135 stack heads (saved incoming T is separate). -/
def pa135Heads (a b c u h : Nat) : List Nat :=
  [rho1 a b,rho2 a b c,rho3 a b c,rho4 a b c,rho5 a b c,
   rho6 a b,rho7 a b c,rho8 a b c u,wal u h]

theorem gate_proved (a b c : Nat) : Proved (gate a b c) := by
  unfold gate
  split
  · exact ⟨.truth⟩
  · rename_i h
    exact ⟨.guardedBundle a b c (fun ha => h (Or.inl ha)) (fun hb => h (Or.inr hb))⟩

/-- The proof-valued AX head interface for the actual dominated source.
No source execution or ordinary-PA calibration is assumed by this lemma. -/
theorem pa135Heads_proved (a b c u h : Nat) (hdom : u ≤ a) (hh : Proved h) :
    ∀ x ∈ pa135Heads a b c u h, Proved x := by
  rcases hh with ⟨dh⟩
  intro x hx
  simp only [pa135Heads,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.r1 a b⟩
  · exact ⟨.r2 a b c⟩
  · exact ⟨.r3 a b c⟩
  · exact ⟨.r4 a b c⟩
  · exact ⟨.r5 a b c⟩
  · exact ⟨.r6 a b⟩
  · exact ⟨.r7 a b c⟩
  · exact ⟨.r8 a b c u hdom⟩
  · exact ⟨.all u dh⟩

theorem mp_proved {a b} (ha : Proved a) (hab : Proved (wim a b)) : Proved b := by
  rcases ha with ⟨da⟩
  rcases hab with ⟨dab⟩
  exact ⟨.mp da dab⟩

#print axioms gate_proved
#print axioms pa135Heads_proved
end M6.PA.NativeCalculus

