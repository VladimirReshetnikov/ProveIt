import BusyBeaver.ZFC.L2Control254
import BusyBeaver.ZFC.L2Macros222

/-! Control contracts of `dag222`. Shared branches transfer from the native 254
library; the rotated next-candidate loop and its fetch composition remain local. -/
namespace SetTheory.BusyBeaver.ZFC.L2K
open RMDag Dag222 Code254
attribute [local irreducible] Code254.P
export L2 (dist dist_eq_zero)

abbrev loop124 (a : Nat) (st : AS) (h : st.s1 = a) :=
  trCore (n := 124) rfl (L2.loop124 a st h)
abbrev ifeq_eq (st : AS) (h : st.s1 = st.p2) := trCore (n := 123) rfl (L2.ifeq_eq st h)
abbrev ifeq_ne (st : AS) (h : st.s1 ≠ st.p2) := trCore (n := 123) rfl (L2.ifeq_ne st h)
abbrev ifeq_par1 (st : AS) (h : st.s2 = 0) := trCore (n := 130) rfl (L2.ifeq_par1 st h)
abbrev ifeq_clear (st : AS) := trCore (n := 131) rfl (L2.ifeq_clear st)

theorem loop136 : ∀ (k : Nat) (st : AS), st.s1 = k →
    Rn (.node 136) st { st with np := st.np + k + 1, s1 := 0 } := by
  have hinc (st : AS) :
      Run dag222 (.inc 0) (enc st) .normal (enc { st with np := st.np + 1 }) := by
    have := Run.inc (p := dag222) 0 (enc st)
    rwa [show enc st 0 = st.np from rfl, upd_np] at this
  intro k
  induction k with
  | zero =>
      intro st h
      have hz : Run dag222 (.decnz 6) (enc { st with np := st.np + 1 }) (.brk 1)
          (enc { st with np := st.np + 1 }) := Run.decZero 6 _ (by simp [enc, h])
      have := Run.cdrNormal (p := dag222) 136 _ _ _ (hinc st) (Run.carBrk1 300 _ _ hz)
      have e : ({ st with np := st.np + 1 } : AS) = { st with np := st.np + 0 + 1, s1 := 0 } := by
        cases st; simp only at h; subst h; rfl
      rwa [e] at this
  | succ k ih =>
      intro st h
      have hdec : Run dag222 (.decnz 6) (enc { st with np := st.np + 1 }) .normal
          (enc { st with np := st.np + 1, s1 := k }) := by
        have := Run.decPos (p := dag222) 6 (enc { st with np := st.np + 1 }) k (by simp [enc, h])
        rwa [upd_s1] at this
      have := Run.cdrCont1 (p := dag222) 136 _ _ _ _ _ (hinc st)
        (Run.cdrContS 300 0 _ _ _ hdec (Run.contS 1 _))
        (ih { st with np := st.np + 1, s1 := k } rfl)
      have e2 : ({ ({ st with np := st.np + 1, s1 := k } : AS) with
          np := (({ st with np := st.np + 1, s1 := k } : AS)).np + k + 1, s1 := 0 } : AS) =
          { st with np := st.np + (k + 1) + 1, s1 := 0 } := by
        cases st; simp only; congr 1; omega
      rwa [e2] at this

theorem fetch_pos (st : AS) (v : Nat) (hv : st.pl = v + 1) : Rn (.node 133) st { st with pl := v } := by
  have hdec := Run.decPos (p := dag222) 8 (enc st) v (by simp [enc, hv])
  rw [upd_pl] at hdec
  have h134 := brk_cdr (p := dag222) (n := 134) (k := 0) rfl hdec (Run.brkS 0 _)
  exact skip (p := dag222) (n := 133) rfl h134

theorem fetch_zero (st : AS) (hpl : st.pl = 0) (h1 : st.s1 = 0) :
    Rn (.node 133) st { st with pl := st.np, np := st.np + 1 } := by
  have h134 : Rn (.node 134) st st :=
    skip (p := dag222) (n := 134) rfl (Run.decZero 8 (enc st) (by simp [enc, hpl]))
  have h135 := seqAS (n := 135) rfl (loop194 st)
    (loop136 _ _ rfl)
  apply rn_eq (seqAS (n := 133) rfl h134 h135)
  cases st; simp only at hpl h1; subst hpl h1; simp

abbrev mp_branch (st : AS) (hc : Clean st) := trCore (n := 150) rfl (L2.mp_branch st hc)
abbrev nip_branch (st : AS) (hc : Clean st) (hh : st.p2 ≠ 1) :=
  trCore (n := 152) rfl (L2.nip_branch st hc hh)
abbrev nip_halt (st : AS) (hc : Clean st) (hh : st.p2 = 1) :
    ∃ R', Run dag222 (.node 152) (enc st) .halt R' :=
  let ⟨R', h⟩ := L2.nip_halt st hc hh
  ⟨R', trCore (n := 152) rfl h⟩

end SetTheory.BusyBeaver.ZFC.L2K
