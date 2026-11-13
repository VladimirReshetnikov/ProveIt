module
public import M6PA.Theory
public import M6PA.Calibration.RelationalSourceAllocation
@[expose] public section

/-! A concrete Foundation first-order logical rule compiled into a finite
actual-basis proof: universal elimination for arbitrary source formulas and
terms. All allocator/replacement guards are discharged from numeric bounds.
This is not the remaining whole LK/PA or induction interpretation. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder NativeCalculus NativeCalculus.ActualBasis

def instantiate {ξ : Type} {n : Nat} (p : Semiformula language ξ (n+1))
    (t : Semiterm language ξ n) : Semiformula language ξ n :=
  Semiformula.rewAux (Rew.subst (Fin.cases t Semiterm.bvar)) p

theorem toNamed_instantiate {ξ : Type} {n : Nat} (p : Semiformula language ξ (n+1))
    (t : Semiterm language ξ n) (b : Fin n → Nat) (f : ξ → Nat) (lo : Nat) :
    toNamed (instantiate p t) b f lo = toNamed p (Fin.cases (termLabel t b f) b) f lo := by
  apply toNamed_rew
  intro u
  cases u with
  | bvar i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  | fvar i => rfl
  | func fn _ => nomatch fn

def universalInstance {ξ : Type} {n : Nat} (p : Semiformula language ξ (n+1))
    (t : Semiterm language ξ n) (b : Fin n → Nat) (f : ξ → Nat) (lo z : Nat)
    (hlo : 0 < lo) (hb : ∀ i,b i < lo) (hf : ∀ i,f i < lo)
    (hz : lo+1+depth p ≤ z) :
    Proof (wim (relationalCode z (toNamed (.all p) b f lo))
      (relationalCode z (toNamed (instantiate p t) b f lo))) := by
  let y := termLabel t b f
  have hy : y < lo := termLabel_lt t b f lo hb hf
  let body := toNamed p (Fin.cases lo b) f (lo+1)
  have hb' : ∀ i,(Fin.cases (motive := fun _ => Nat) lo b) i < lo+1 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa using Nat.lt_trans (hb j) (Nat.lt_succ_self lo)
  have hf' : ∀ i,f i < lo+1 := fun i => Nat.lt_trans (hf i) (Nat.lt_succ_self lo)
  have hreserved : body.names z = false :=
    toNamed_reserved p (Fin.cases lo b) f (lo+1) z (by omega) hb' hf' hz
  have hxb : body.binders lo = false := toNamed_binders_below p _ f _ _ (by omega)
  have hyb : body.binders y = false := toNamed_binders_below p _ f _ _ (by omega)
  let hi := relationalUniversalInstance body z lo y (by omega) hreserved (by omega) (by omega) hxb hyb
  have hbRename : renameLabel lo y ∘ Fin.cases lo b = Fin.cases y b := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [renameLabel]
    · simp [renameLabel,Nat.ne_of_lt (hb j)]
  have hfRename : renameLabel lo y ∘ f = f := by
    funext i
    simp [renameLabel,Nat.ne_of_lt (hf i)]
  have hrepl : body.replace lo y = toNamed p (Fin.cases y b) f (lo+1) := by
    simp only [body,toNamed_replace p (Fin.cases lo b) f (lo+1) lo y (by omega) (by omega),hbRename,hfRename]
  rw [hrepl] at hi
  have hby : ∀ i,(Fin.cases (motive := fun _ => Nat) y b) i < min (lo+1) lo := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hy
    · simpa using hb j
  have hfy : ∀ i,f i < min (lo+1) lo := by intro i; simpa using hf i
  let hr := reallocation p (Fin.cases y b) f (lo+1) lo z (by omega) hlo hby hfy (by omega)
  simpa only [toNamed,relationalCode,toNamed_instantiate,body,y] using implicationCompose hi hr.1

#print axioms toNamed_instantiate
#print axioms universalInstance
end M6.PA.RelationalSource

