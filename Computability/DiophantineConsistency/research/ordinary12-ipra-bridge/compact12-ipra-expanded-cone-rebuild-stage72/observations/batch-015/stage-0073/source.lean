import BusyBeaver.ZFC.TarskiCalculus
import BusyBeaver.ZFC.ProfileSyntax

/-!
Exact named-formula to de Bruijn translation, with native equality.

Each binder moves its named variable to slot0 and shifts all other names.
This handles repeated/shadowed binders and all variable maps without an
injectivity or freshness assumption. Genuine Bottom remains Bottom; no
relative-falsity or irreflexivity hypothesis is needed for this direction.

The matrix adapter assigns input/output slots to arbitrary names a,b, with
output precedence when a=b, exactly matching nested named updates. It does
not claim the resulting matrix is equality-free, or that equality-free GIC
can be applied to a native-equality matrix.
-/

namespace SetTheory.BusyBeaver.ZFC.NamedForm254

open Tarski (NF)
open Form

def under (slots : Nat → Nat) (binder : Nat) (i : Nat) : Nat :=
  if i = binder then 0 else slots i + 1

def translate (slots : Nat → Nat) : NF → Form
  | .rel i j => fMem (slots i) (slots j)
  | .eq i j => fEq (slots i) (slots j)
  | .bot => fBot
  | .imp f g => fImp (translate slots f) (translate slots g)
  | .all i f => fAll (translate (under slots i) f)

universe u
variable {V : Type u}

theorem under_env (slots : Nat → Nat) (binder : Nat) (env : Nat → V) (x : V) :
    (fun i => scons x env (under slots binder i)) =
      Tarski.update (fun i => env (slots i)) binder x := by
  funext i
  by_cases h : i = binder <;> simp [under, Tarski.update, h, scons]

/-- The compiler preserves named satisfaction for an arbitrary slot map. -/
theorem sat_translate (mem : V → V → Prop) (f : NF) (slots : Nat → Nat)
    (env : Nat → V) :
    SetTheory.Sat mem env (translate slots f) ↔
      Tarski.Sat mem (fun i => env (slots i)) f := by
  induction f generalizing slots env with
  | rel i j | eq i j | bot => rfl
  | imp f g hf hg => exact imp_congr (hf slots env) (hg slots env)
  | all i f ih =>
    change (∀ x, SetTheory.Sat mem (scons x env) (translate (under slots i) f)) ↔ _
    exact forall_congr' fun x => (ih (under slots i) (scons x env)).trans (by rw [under_env])

/-- Slot0 is input, slot1 is output, and slot2+i retains parameter name i. -/
def matrixSlots (a b i : Nat) : Nat :=
  if i = b then 1 else if i = a then 0 else i + 2

def matrix (f : NF) (a b : Nat) : Form := translate (matrixSlots a b) f

theorem matrix_env (a b : Nat) (env : Nat → V) (x y : V) :
    (fun i => scons x (scons y env) (matrixSlots a b i)) =
      Tarski.update (Tarski.update env a x) b y := by
  funext i
  simp only [matrixSlots, Tarski.update]
  by_cases hb : i = b
  · simp only [if_pos hb]; rfl
  · simp only [if_neg hb]
    by_cases ha : i = a
    · simp only [if_pos ha]; rfl
    · simp only [if_neg ha]; rfl

/-- The source schema's actual MatrixRelation, including the case a=b. -/
theorem sat_matrix (mem : V → V → Prop) (f : NF) (a b : Nat)
    (env : Nat → V) (x y : V) :
    DeepPositiveClosure.MatrixRelation mem (matrix f a b) env x y ↔
      Tarski.Sat mem (Tarski.update (Tarski.update env a x) b y) f :=
  (sat_translate mem f (matrixSlots a b) (scons x (scons y env))).trans
    (by rw [matrix_env])

/-- No equality-free claim can hold for this translation's native equality atom. -/
theorem native_eq_matrix (a b i j : Nat) :
    matrix (.eq i j) a b = fEq (matrixSlots a b i) (matrixSlots a b j) := rfl

end SetTheory.BusyBeaver.ZFC.NamedForm254
