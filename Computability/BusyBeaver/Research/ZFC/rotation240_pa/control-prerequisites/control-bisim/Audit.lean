import BusyBeaver.ZFC.ArithmeticControlBisim

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim.vget_bump
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim.vget_vnorm
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim.checkFrom_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim.entryOK_spec
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim.shifted_bump
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim.shifted_decrement
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim.shifted_norm
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim.segment_sound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim.halts_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlBisim.halts_iff_of_check

example (u : Vec) (r p : Nat) :
    vget (bump u r) p = vget u p + if p = r then 1 else 0 := vget_bump u r p
example (u v : Vec) (p : Fin 9) :
    vget (vnorm u v) p = vget u p - min (vget u p) (vget v p) := vget_vnorm u v p
example (rowsA rowsB : Nat → Option Row) (cert : Nat → Option Entry)
    (fuel bound i k : Nat) (h : checkFrom rowsA rowsB cert fuel bound i k = true)
    (j : Nat) (hj : i ≤ j) (hjk : j < i+k) : entryOK rowsA rowsB cert fuel bound j = true :=
  checkFrom_entry rowsA rowsB cert fuel bound i k h j hj hjk
example (rowsA rowsB : Nat → Option Row) (cert : Nat → Option Entry)
    (fuel bound i : Nat) (h : entryOK rowsA rowsB cert fuel bound i = true) :
    ∃ e, cert i = some e ∧ checkEntry rowsA rowsB cert fuel e = true ∧
      e.s0 < bound ∧ e.s1 < bound ∧ 0 < e.a := entryOK_spec rowsA rowsB cert fuel bound i h

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (reg : V → Fin 9 → V) (write : Fin 9 → V → V → V) (live : V → V → V)
  (reg_write_same : ∀ p v x, reg (write p v x) p = v)
  (reg_write_other : ∀ p q v x, p ≠ q → reg (write p v x) q = reg x q)

example (x y : V) (u : Vec) (r : Fin 9) (h : Shifted reg x u y) :
    Shifted reg x (bump u r) (write r (reg y r+1) y) :=
  shifted_bump reg_write_same reg_write_other x y u r h
example (x y : V) (u : Vec) (r : Fin 9) (h : Shifted reg x u y) (hu : vget u r = 0) :
    Shifted reg (write r (reg x r-1) x) u (write r (reg y r-1) y) :=
  shifted_decrement reg_write_same reg_write_other x y u r h hu
example (x ya yb : V) (ua ub : Vec) (ha : Shifted reg x ua ya) (hb : Shifted reg x ub yb)
    (x' : V) (hx' : ∀ p : Fin 9, reg x' p = reg x p + ((min (vget ua p) (vget ub p) : Nat) : V)) :
    Shifted reg x' (vnorm ua ub) ya ∧ Shifted reg x' (vnorm ub ua) yb :=
  shifted_norm x ya yb ua ub ha hb x' hx'

example (step : V → V) (run : V → V → V) (rows : Nat → Option Row)
    (run_zero : ∀ x, run 0 x = x)
    (run_add : ∀ t u x, run (t+u) x = run u (run t x))
    (run_one : ∀ x, run 1 x = step x)
    (spec : ∀ (c : Nat) (row : Row) (x : V), rows c = some row →
      step (live (c : V) x) = sem reg write live row x)
    (fuel c : Nat) (u : Vec) (t : Nat) (u' : Vec)
    (hs : segment rows fuel c u = some (t,u')) (x y : V) (hy : Shifted reg x u y) :
    ∃ k y', run k (live (c : V) y) = live (t : V) y' ∧ Shifted reg x u' y' :=
  segment_sound step run rows run_zero run_add run_one spec
    reg_write_same reg_write_other fuel c u t u' hs x y hy

example (runA runB : V → V → V) (R : V → V → Prop)
    [𝚺₁-Function₂[V] runA] [𝚺₁-Function₂[V] runB] [𝚺₁-Relation[V] R]
    (az : ∀ x, runA 0 x = x) (bz : ∀ x, runB 0 x = x)
    (aa : ∀ t u x, runA (t+u) x = runA u (runA t x))
    (ba : ∀ t u x, runB (t+u) x = runB u (runB t x))
    (ah : ∀ t, runA t 0 = 0) (bh : ∀ t, runB t 0 = 0)
    (rlive : ∀ a b, R a b → a ≠ 0 ∧ b ≠ 0)
    (rstep : ∀ a b, R a b → ∃ ka kb, 1 ≤ ka ∧ 1 ≤ kb ∧
      ((runA ka a = 0 ∧ runB kb b = 0) ∨ R (runA ka a) (runB kb b)))
    (a0 b0 : V) (h0 : R a0 b0) :
    (∃ t, runA t a0 = 0) ↔ (∃ t, runB t b0 = 0) :=
  halts_iff runA runB R az bz aa ba ah bh rlive rstep a0 b0 h0

/-- Every abstract certificate and file law remains a premise. No concrete certificate is asserted. -/
example (fileOf : (Fin 9 → V) → V) (reg_fileOf : ∀ g p, reg (fileOf g) p = g p)
    (live_ne : ∀ c x, live c x ≠ 0)
    (liveDef : 𝚺₁.Semisentence 3) (regDef : Fin 9 → 𝚺₁.Semisentence 2)
    [𝚺₁-Function₂[V] live via liveDef]
    [∀ p, 𝚺₁-Function₁[V] (fun x => reg x p) via regDef p]
    (stepA stepB : V → V) (runA runB : V → V → V)
    [𝚺₁-Function₂[V] runA] [𝚺₁-Function₂[V] runB]
    (rowsA rowsB : Nat → Option Row) (cert : Nat → Option Entry) (fuel N : Nat)
    (az : ∀ x, runA 0 x = x) (bz : ∀ x, runB 0 x = x)
    (aa : ∀ t u x, runA (t+u) x = runA u (runA t x))
    (ba : ∀ t u x, runB (t+u) x = runB u (runB t x))
    (aone : ∀ x, runA 1 x = stepA x) (bone : ∀ x, runB 1 x = stepB x)
    (ah : ∀ t, runA t 0 = 0) (bh : ∀ t, runB t 0 = 0)
    (specA : ∀ (c : Nat) (row : Row) (x : V), rowsA c = some row →
      stepA (live (c : V) x) = sem reg write live row x)
    (specB : ∀ (c : Nat) (row : Row) (x : V), rowsB c = some row →
      stepB (live (c : V) x) = sem reg write live row x)
    (hcheck : ∀ i, i < N → entryOK rowsA rowsB cert fuel N i = true)
    (e : Entry) (he : cert 0 = some e) (hN : 0 < N)
    (hα : ∀ p : Fin 9, vget e.α p = 0) (hβ : ∀ p : Fin 9, vget e.β p = 0) (x : V) :
    (∃ t, runA t (live (e.a : V) x) = 0) ↔ (∃ t, runB t (live (e.b : V) x) = 0) :=
  halts_iff_of_check fileOf reg_fileOf live_ne liveDef regDef stepA stepB runA runB
    rowsA rowsB cert fuel N az bz aa ba aone bone ah bh specA specB
    reg_write_same reg_write_other hcheck e he hN hα hβ x
end Model
