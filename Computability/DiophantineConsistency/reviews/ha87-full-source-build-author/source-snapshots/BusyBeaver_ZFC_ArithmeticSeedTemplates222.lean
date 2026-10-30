import BusyBeaver.ZFC.ArithmeticTemplates222

set_option autoImplicit false
set_option Elab.async false

/-! The helper-free C222 seed as fixed bounded constructor circuits. These
are code/graph identities, not a proof that the seed is internally valid. -/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSeedTemplates222

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCode254 ArithmeticTemplates254
open ArithmeticTemplates254.Circuit

def reqC (b k m : Circuit) : Circuit :=
  al b (im m (neg (al b (im m (neg (el b k))))))

def closC (a b k m : Circuit) : Circuit :=
  al b (im (el b k) (neg (al a (im m (neg (al a
    (im (al k (im (el k a) (el k b))) (reqC b k m))))))))

def nksC (a b c : Circuit) : Circuit :=
  al c (im (closC a b c c) (neg (reqC b c c)))

def vrelC (a b c : Circuit) : Circuit := im (el a b) (al c (el a b))

def bundleC (a b c : Circuit) : Circuit := neg (im (vrelC a b c) (nksC a b c))

def reqTemplate : Circuit := reqC input0 input1 input2
def closTemplate : Circuit := closC input0 input1 input2 input3
def nksTemplate : Circuit := nksC input0 input1 input2
def vrelTemplate : Circuit := vrelC input0 input1 input2
def bundleTemplate : Circuit := bundleC input0 input1 input2

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def req (b k m : V) : V := reqTemplate.eval b k m 0
noncomputable def clos (a b k m : V) : V := closTemplate.eval a b k m
noncomputable def nks (a b c : V) : V := nksTemplate.eval a b c 0
noncomputable def vrel (a b c : V) : V := vrelTemplate.eval a b c 0
noncomputable def bundle222 (a b c : V) : V := bundleTemplate.eval a b c 0

theorem req_eq (b k m : V) : req b k m =
    wal b (wim m (wim (wal b (wim m (wim (wel b k) 1))) 1)) := rfl

theorem clos_eq (a b k m : V) : clos a b k m =
    wal b (wim (wel b k) (wim (wal a (wim m (wim (wal a
      (wim (wal k (wim (wel k a) (wel k b))) (req b k m))) 1))) 1)) := rfl

theorem nks_eq (a b c : V) :
    nks a b c = wal c (wim (clos a b c c) (wim (req b c c) 1)) := rfl

theorem vrel_eq (a b c : V) : vrel a b c = wim (wel a b) (wal c (wel a b)) := rfl

/-- Every relative negation retains the actual false code1. -/
theorem bundle222_eq (a b c : V) :
    bundle222 a b c = wim (wim (vrel a b c) (nks a b c)) 1 := rfl

def reqDef : 𝚺₀.Semisentence 4 := .mkSigma
  “r b k m. !(reqTemplate.graph) r b k m 0”
def closDef : 𝚺₀.Semisentence 5 := .mkSigma
  “r a b k m. !(closTemplate.graph) r a b k m”
def nksDef : 𝚺₀.Semisentence 4 := .mkSigma
  “r a b c. !(nksTemplate.graph) r a b c 0”
def vrelDef : 𝚺₀.Semisentence 4 := .mkSigma
  “r a b c. !(vrelTemplate.graph) r a b c 0”
def bundleDef : 𝚺₀.Semisentence 4 := .mkSigma
  “r a b c. !(bundleTemplate.graph) r a b c 0”

instance req_defined : 𝚺₀-Function₃[V] req via reqDef :=
  .mk fun v => by simp [reqDef, req]
instance clos_defined : 𝚺₀-Function₄[V] clos via closDef :=
  .mk fun v => by simp [closDef, clos]
instance nks_defined : 𝚺₀-Function₃[V] nks via nksDef :=
  .mk fun v => by simp [nksDef, nks]
instance vrel_defined : 𝚺₀-Function₃[V] vrel via vrelDef :=
  .mk fun v => by simp [vrelDef, vrel]
instance bundle_defined : 𝚺₀-Function₃[V] bundle222 via bundleDef :=
  .mk fun v => by simp [bundleDef, bundle222]

@[simp] theorem req_nat (b k m : Nat) : req b k m = KCode222.req b k m := by
  simp only [req_eq, wal_nat, wim_nat, wel_nat, KCode222.req, Code254.wn, Code254.F]

@[simp] theorem clos_nat (a b k m : Nat) : clos a b k m = KCode222.clos a b k m := by
  simp only [clos_eq, req_nat, wal_nat, wim_nat, wel_nat, KCode222.clos, Code254.wn, Code254.F]

@[simp] theorem nks_nat (a b c : Nat) : nks a b c = KCode222.nks a b c := by
  simp only [nks_eq, clos_nat, req_nat, wal_nat, wim_nat, KCode222.nks, Code254.wn, Code254.F]

@[simp] theorem vrel_nat (a b c : Nat) : vrel a b c = KCode222.vrel a b c := by
  simp only [vrel_eq, wal_nat, wim_nat, wel_nat, KCode222.vrel]

@[simp] theorem bundle222_nat (a b c : Nat) :
    bundle222 a b c = KCode222.bundle222 a b c := by
  simp only [bundle222_eq, vrel_nat, nks_nat, wim_nat, KCode222.bundle222, Code254.wn, Code254.F]

instance codeBundle_defined : HierarchySymbol.DefinedFunction₃ (V := Nat) 𝚺₀
    KCode222.bundle222 bundleDef := by
  have h : (bundle222 : Nat → Nat → Nat → Nat) = KCode222.bundle222 :=
    funext fun a => funext fun b => funext fun c => bundle222_nat a b c
  rw [← h]
  exact bundle_defined

end SetTheory.BusyBeaver.ZFC.ArithmeticSeedTemplates222
