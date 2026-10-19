import BusyBeaver.ZFC.ArithmeticL2Control254

set_option autoImplicit false

/-!
# Internal L2, part 4: the `axioms()` routine of the 219-node program

The internal counterpart of `L2Axioms254`, in every model of `IΣ₁`: one
lemma per node of the `axioms()` subtree, each composing the effects of its
two children, ported mechanically from the external module by
`Research/ZFC/rotation240_pa/port_l2_axioms.py` (records over the model,
the internal Cantor pairing and constructors, the internal structured-run
rules). The final gate (node 71) is proved by hand.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticL2

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticDagRun RMDag
open ArithmeticCode254 (wim wel wal weq)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


noncomputable def pushF (st : AS V) : AS V := { st with tw := 0, ws := cantor st.tw st.ws }
noncomputable def par1F (st : AS V) : AS V := { st with tw := st.p1, ws := cantor st.tw st.ws }
noncomputable def par2F (st : AS V) : AS V := { st with tw := st.p2, ws := cantor st.tw st.ws }
noncomputable def par3F (st : AS V) : AS V := { st with tw := st.ac, ws := cantor st.tw st.ws }
noncomputable def consF (st : AS V) : AS V :=
  { st with tw := wim (first st.ws) st.tw, ws := (second st.ws) }
noncomputable def welF (st : AS V) : AS V :=
  { st with tw := wel (first st.ws) st.tw, ws := (second st.ws) }
noncomputable def walF (st : AS V) : AS V :=
  { st with tw := wal (first st.ws) st.tw, ws := (second st.ws) }
noncomputable def weqF (st : AS V) : AS V :=
  { st with tw := weq (first st.ws) st.tw, ws := (second st.ws) }
noncomputable def wnF (st : AS V) : AS V := { st with tw := wn st.tw }
noncomputable def waF (st : AS V) : AS V :=
  { st with tw := wa (first st.ws) st.tw, ws := (second st.ws) }
noncomputable def wexF (st : AS V) : AS V :=
  { st with tw := wex (first st.ws) st.tw, ws := (second st.ws) }
noncomputable def readp2F (st : AS V) : AS V :=
  { st with pl := (second st.pl), p2 := st.p2 + (first st.pl) }

theorem pushL (st : AS V) (hc : Clean st) : Rn (.node 171) st (pushF st) := pushwff st hc
theorem par1L (st : AS V) (hc : Clean st) : Rn (.node 166) st (par1F st) := par1 st hc
theorem par2L (st : AS V) (hc : Clean st) : Rn (.node 121) st (par2F st) := par2 st hc
theorem par3L (st : AS V) (hc : Clean st) : Rn (.node 168) st (par3F st) := par3 st hc
theorem consL (st : AS V) (hc : Clean st) : Rn (.node 119) st (consF st) := cons st hc
theorem welL (st : AS V) (hc : Clean st) : Rn (.node 181) st (welF st) := wel_m st hc
theorem walL (st : AS V) (hc : Clean st) : Rn (.node 180) st (walF st) := wal_m st hc
theorem weqL (st : AS V) (hc : Clean st) : Rn (.node 182) st (weqF st) := weq_m st hc
theorem wnL (st : AS V) (hc : Clean st) : Rn (.node 218) st (wnF st) := wn_m st hc
theorem waL (st : AS V) (hc : Clean st) : Rn (.node 178) st (waF st) := wa_m st hc
theorem wexL (st : AS V) (hc : Clean st) : Rn (.node 183) st (wexF st) := wex_m st hc
theorem readp2L (st : AS V) (hc : Clean st) : Rn (.node 176) st (readp2F st) := read_p2 st hc

theorem pushC (st : AS V) (hc : Clean st) : Clean (pushF st) := hc
theorem par1C (st : AS V) (hc : Clean st) : Clean (par1F st) := hc
theorem par2C (st : AS V) (hc : Clean st) : Clean (par2F st) := hc
theorem par3C (st : AS V) (hc : Clean st) : Clean (par3F st) := hc
theorem consC (st : AS V) (hc : Clean st) : Clean (consF st) := hc
theorem welC (st : AS V) (hc : Clean st) : Clean (welF st) := hc
theorem walC (st : AS V) (hc : Clean st) : Clean (walF st) := hc
theorem weqC (st : AS V) (hc : Clean st) : Clean (weqF st) := hc
theorem wnC (st : AS V) (hc : Clean st) : Clean (wnF st) := hc
theorem waC (st : AS V) (hc : Clean st) : Clean (waF st) := hc
theorem wexC (st : AS V) (hc : Clean st) : Clean (wexF st) := hc
theorem readp2C (st : AS V) (hc : Clean st) : Clean (readp2F st) := hc

/-- The gate (node 71): clear the bundle when `c = b` or `c = a`, and clear
`axiomcode`, `param1`, `param2`. -/
noncomputable def gateF (st : AS V) : AS V :=
  { st with ac := 0, p1 := 0, p2 := 0, tw := if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else st.tw }

theorem gateC (st : AS V) (hc : Clean st) : Clean (gateF st) := hc

theorem l71 (st : AS V) (hc : Clean st) : Rn (.node 71) st (gateF st) := by
  have := R.seq (n := 71) rfl (loop192 st) (R.seq (n := 72) rfl (ifeq_clear _)
    (R.seq (n := 73) rfl (loop211 _) (R.seq (n := 74) rfl (loop197 _) (ifeq_clear _))))
  apply rn_eq this
  obtain ⟨h1, h2⟩ := hc
  rcases st with ⟨np, tw, ws, ac, p1, p2, s1, s2, pl⟩
  simp only at h1 h2
  subst h1; subst h2
  simp only [gateF, zero_add]
  split_ifs <;> simp_all

/-- node_111.0 -/
noncomputable def f161 (st : AS V) : AS V := consF (par1F st)
theorem l161 (st : AS V) (hc : Clean st) : Rn (.node 161) st (f161 st) :=
  R.seq (n := 161) rfl (par1L st hc) (consL _ (par1C st hc))
theorem c161 (st : AS V) (hc : Clean st) : Clean (f161 st) :=
  consC _ (par1C st hc)

/-- axioms().n_112.0 -/
noncomputable def f104 (st : AS V) : AS V := consF (par3F st)
theorem l104 (st : AS V) (hc : Clean st) : Rn (.node 104) st (f104 st) :=
  R.seq (n := 104) rfl (par3L st hc) (consL _ (par3C st hc))
theorem c104 (st : AS V) (hc : Clean st) : Clean (f104 st) :=
  consC _ (par3C st hc)

/-- axioms().n_119.0 -/
noncomputable def f111 (st : AS V) : AS V := par1F (par3F st)
theorem l111 (st : AS V) (hc : Clean st) : Rn (.node 111) st (f111 st) :=
  R.seq (n := 111) rfl (par3L st hc) (par1L _ (par3C st hc))
theorem c111 (st : AS V) (hc : Clean st) : Clean (f111 st) :=
  par1C _ (par3C st hc)

/-- axioms().n_122.0 -/
noncomputable def f114 (st : AS V) : AS V := par2F (par3F st)
theorem l114 (st : AS V) (hc : Clean st) : Rn (.node 114) st (f114 st) :=
  R.seq (n := 114) rfl (par3L st hc) (par2L _ (par3C st hc))
theorem c114 (st : AS V) (hc : Clean st) : Clean (f114 st) :=
  par2C _ (par3C st hc)

/-- axioms().n_094.2 -/
noncomputable def f89 (st : AS V) : AS V := f114 (weqF st)
theorem l89 (st : AS V) (hc : Clean st) : Rn (.node 89) st (f89 st) :=
  R.seq (n := 89) rfl (weqL st hc) (l114 _ (weqC st hc))
theorem c89 (st : AS V) (hc : Clean st) : Clean (f89 st) :=
  c114 _ (weqC st hc)

/-- axioms().n_094.1 -/
noncomputable def f88 (st : AS V) : AS V := f89 (f111 st)
theorem l88 (st : AS V) (hc : Clean st) : Rn (.node 88) st (f88 st) :=
  R.seq (n := 88) rfl (l111 st hc) (l89 _ (c111 st hc))
theorem c88 (st : AS V) (hc : Clean st) : Clean (f88 st) :=
  c89 _ (c111 st hc)

/-- axioms().n_094.0 -/
noncomputable def f87 (st : AS V) : AS V := f88 (consF st)
theorem l87 (st : AS V) (hc : Clean st) : Rn (.node 87) st (f87 st) :=
  R.seq (n := 87) rfl (consL st hc) (l88 _ (consC st hc))
theorem c87 (st : AS V) (hc : Clean st) : Clean (f87 st) :=
  c88 _ (consC st hc)

/-- axioms().n_116.0 -/
noncomputable def f108 (st : AS V) : AS V := weqF (par2F st)
theorem l108 (st : AS V) (hc : Clean st) : Rn (.node 108) st (f108 st) :=
  R.seq (n := 108) rfl (par2L st hc) (weqL _ (par2C st hc))
theorem c108 (st : AS V) (hc : Clean st) : Clean (f108 st) :=
  weqC _ (par2C st hc)

/-- axioms().n_121.0 -/
noncomputable def f113 (st : AS V) : AS V := par2F (par1F st)
theorem l113 (st : AS V) (hc : Clean st) : Rn (.node 113) st (f113 st) :=
  R.seq (n := 113) rfl (par1L st hc) (par2L _ (par1C st hc))
theorem c113 (st : AS V) (hc : Clean st) : Clean (f113 st) :=
  par2C _ (par1C st hc)

/-- axioms().n_106.0 -/
noncomputable def f102 (st : AS V) : AS V := f113 (par1F st)
theorem l102 (st : AS V) (hc : Clean st) : Rn (.node 102) st (f102 st) :=
  R.seq (n := 102) rfl (par1L st hc) (l113 _ (par1C st hc))
theorem c102 (st : AS V) (hc : Clean st) : Clean (f102 st) :=
  c113 _ (par1C st hc)

/-- axioms().n_095.1 -/
noncomputable def f91 (st : AS V) : AS V := f102 (consF st)
theorem l91 (st : AS V) (hc : Clean st) : Rn (.node 91) st (f91 st) :=
  R.seq (n := 91) rfl (consL st hc) (l102 _ (consC st hc))
theorem c91 (st : AS V) (hc : Clean st) : Clean (f91 st) :=
  c102 _ (consC st hc)

/-- axioms().n_095.0 -/
noncomputable def f90 (st : AS V) : AS V := f91 (consF st)
theorem l90 (st : AS V) (hc : Clean st) : Rn (.node 90) st (f90 st) :=
  R.seq (n := 90) rfl (consL st hc) (l91 _ (consC st hc))
theorem c90 (st : AS V) (hc : Clean st) : Clean (f90 st) :=
  c91 _ (consC st hc)

/-- axioms().n_113.0 -/
noncomputable def f105 (st : AS V) : AS V := par2F (wexF st)
theorem l105 (st : AS V) (hc : Clean st) : Rn (.node 105) st (f105 st) :=
  R.seq (n := 105) rfl (wexL st hc) (par2L _ (wexC st hc))
theorem c105 (st : AS V) (hc : Clean st) : Clean (f105 st) :=
  par2C _ (wexC st hc)

/-- axioms().n_117.0 -/
noncomputable def f109 (st : AS V) : AS V := welF (par2F st)
theorem l109 (st : AS V) (hc : Clean st) : Rn (.node 109) st (f109 st) :=
  R.seq (n := 109) rfl (par2L st hc) (welL _ (par2C st hc))
theorem c109 (st : AS V) (hc : Clean st) : Clean (f109 st) :=
  welC _ (par2C st hc)

/-- axioms().n_105.0 -/
noncomputable def f101 (st : AS V) : AS V := f113 (consF st)
theorem l101 (st : AS V) (hc : Clean st) : Rn (.node 101) st (f101 st) :=
  R.seq (n := 101) rfl (consL st hc) (l113 _ (consC st hc))
theorem c101 (st : AS V) (hc : Clean st) : Clean (f101 st) :=
  c113 _ (consC st hc)

/-- axioms().n_092.2 -/
noncomputable def f83 (st : AS V) : AS V := par3F (f101 st)
theorem l83 (st : AS V) (hc : Clean st) : Rn (.node 83) st (f83 st) :=
  R.seq (n := 83) rfl (l101 st hc) (par3L _ (c101 st hc))
theorem c83 (st : AS V) (hc : Clean st) : Clean (f83 st) :=
  par3C _ (c101 st hc)

/-- axioms().n_092.1 -/
noncomputable def f82 (st : AS V) : AS V := f83 (consF st)
theorem l82 (st : AS V) (hc : Clean st) : Rn (.node 82) st (f82 st) :=
  R.seq (n := 82) rfl (consL st hc) (l83 _ (consC st hc))
theorem c82 (st : AS V) (hc : Clean st) : Clean (f82 st) :=
  c83 _ (consC st hc)

/-- axioms().n_092.0 -/
noncomputable def f81 (st : AS V) : AS V := f82 (f109 st)
theorem l81 (st : AS V) (hc : Clean st) : Rn (.node 81) st (f81 st) :=
  R.seq (n := 81) rfl (l109 st hc) (l82 _ (c109 st hc))
theorem c81 (st : AS V) (hc : Clean st) : Clean (f81 st) :=
  c82 _ (c109 st hc)

/-- axioms().n_120.0 -/
noncomputable def f112 (st : AS V) : AS V := par3F (par1F st)
theorem l112 (st : AS V) (hc : Clean st) : Rn (.node 112) st (f112 st) :=
  R.seq (n := 112) rfl (par1L st hc) (par3L _ (par1C st hc))
theorem c112 (st : AS V) (hc : Clean st) : Clean (f112 st) :=
  par3C _ (par1C st hc)

/-- axioms().n_101.0 -/
noncomputable def f96 (st : AS V) : AS V := walF (f112 st)
theorem l96 (st : AS V) (hc : Clean st) : Rn (.node 96) st (f96 st) :=
  R.seq (n := 96) rfl (l112 st hc) (walL _ (c112 st hc))
theorem c96 (st : AS V) (hc : Clean st) : Clean (f96 st) :=
  walC _ (c112 st hc)

/-- axioms().n_093.2 -/
noncomputable def f86 (st : AS V) : AS V := f111 (weqF st)
theorem l86 (st : AS V) (hc : Clean st) : Rn (.node 86) st (f86 st) :=
  R.seq (n := 86) rfl (weqL st hc) (l111 _ (weqC st hc))
theorem c86 (st : AS V) (hc : Clean st) : Clean (f86 st) :=
  c111 _ (weqC st hc)

/-- axioms().n_093.1 -/
noncomputable def f85 (st : AS V) : AS V := f86 (f101 st)
theorem l85 (st : AS V) (hc : Clean st) : Rn (.node 85) st (f85 st) :=
  R.seq (n := 85) rfl (l101 st hc) (l86 _ (c101 st hc))
theorem c85 (st : AS V) (hc : Clean st) : Clean (f85 st) :=
  c86 _ (c101 st hc)

/-- axioms().n_093.0 -/
noncomputable def f84 (st : AS V) : AS V := f85 (walF st)
theorem l84 (st : AS V) (hc : Clean st) : Rn (.node 84) st (f84 st) :=
  R.seq (n := 84) rfl (walL st hc) (l85 _ (walC st hc))
theorem c84 (st : AS V) (hc : Clean st) : Clean (f84 st) :=
  c85 _ (walC st hc)

/-- axioms().n_114.0 -/
noncomputable def f106 (st : AS V) : AS V := par3F (welF st)
theorem l106 (st : AS V) (hc : Clean st) : Rn (.node 106) st (f106 st) :=
  R.seq (n := 106) rfl (welL st hc) (par3L _ (welC st hc))
theorem c106 (st : AS V) (hc : Clean st) : Clean (f106 st) :=
  par3C _ (welC st hc)

/-- axioms().n_115.0 -/
noncomputable def f107 (st : AS V) : AS V := walF (consF st)
theorem l107 (st : AS V) (hc : Clean st) : Rn (.node 107) st (f107 st) :=
  R.seq (n := 107) rfl (consL st hc) (walL _ (consC st hc))
theorem c107 (st : AS V) (hc : Clean st) : Clean (f107 st) :=
  walC _ (consC st hc)

/-- axioms().n_100.0 -/
noncomputable def f95 (st : AS V) : AS V := walF (f113 st)
theorem l95 (st : AS V) (hc : Clean st) : Rn (.node 95) st (f95 st) :=
  R.seq (n := 95) rfl (l113 st hc) (walL _ (c113 st hc))
theorem c95 (st : AS V) (hc : Clean st) : Clean (f95 st) :=
  walC _ (c113 st hc)

/-- axioms().n_096.0 -/
noncomputable def f92 (st : AS V) : AS V := welF (f102 st)
theorem l92 (st : AS V) (hc : Clean st) : Rn (.node 92) st (f92 st) :=
  R.seq (n := 92) rfl (l102 st hc) (welL _ (c102 st hc))
theorem c92 (st : AS V) (hc : Clean st) : Clean (f92 st) :=
  welC _ (c102 st hc)

/-- axioms().n_107.0 -/
noncomputable def f103 (st : AS V) : AS V := par3F (f114 st)
theorem l103 (st : AS V) (hc : Clean st) : Rn (.node 103) st (f103 st) :=
  R.seq (n := 103) rfl (l114 st hc) (par3L _ (c114 st hc))
theorem c103 (st : AS V) (hc : Clean st) : Clean (f103 st) :=
  par3C _ (c114 st hc)

/-- axioms().n_098.1 -/
noncomputable def f94 (st : AS V) : AS V := par1F (f106 st)
theorem l94 (st : AS V) (hc : Clean st) : Rn (.node 94) st (f94 st) :=
  R.seq (n := 94) rfl (l106 st hc) (par1L _ (c106 st hc))
theorem c94 (st : AS V) (hc : Clean st) : Clean (f94 st) :=
  par1C _ (c106 st hc)

/-- axioms().n_098.0 -/
noncomputable def f93 (st : AS V) : AS V := f94 (par2F st)
theorem l93 (st : AS V) (hc : Clean st) : Rn (.node 93) st (f93 st) :=
  R.seq (n := 93) rfl (par2L st hc) (l94 _ (par2C st hc))
theorem c93 (st : AS V) (hc : Clean st) : Clean (f93 st) :=
  c94 _ (par2C st hc)

/-- axioms().n_102.0 -/
noncomputable def f97 (st : AS V) : AS V := f107 (welF st)
theorem l97 (st : AS V) (hc : Clean st) : Rn (.node 97) st (f97 st) :=
  R.seq (n := 97) rfl (welL st hc) (l107 _ (welC st hc))
theorem c97 (st : AS V) (hc : Clean st) : Clean (f97 st) :=
  c107 _ (welC st hc)

/-- axioms().n_103.1 -/
noncomputable def f99 (st : AS V) : AS V := welF (par3F st)
theorem l99 (st : AS V) (hc : Clean st) : Rn (.node 99) st (f99 st) :=
  R.seq (n := 99) rfl (par3L st hc) (welL _ (par3C st hc))
theorem c99 (st : AS V) (hc : Clean st) : Clean (f99 st) :=
  welC _ (par3C st hc)

/-- axioms().n_103.0 -/
noncomputable def f98 (st : AS V) : AS V := f99 (par2F st)
theorem l98 (st : AS V) (hc : Clean st) : Rn (.node 98) st (f98 st) :=
  R.seq (n := 98) rfl (par2L st hc) (l99 _ (par2C st hc))
theorem c98 (st : AS V) (hc : Clean st) : Clean (f98 st) :=
  c99 _ (par2C st hc)

/-- axioms().n_118.0 -/
noncomputable def f110 (st : AS V) : AS V := wexF (waF st)
theorem l110 (st : AS V) (hc : Clean st) : Rn (.node 110) st (f110 st) :=
  R.seq (n := 110) rfl (waL st hc) (wexL _ (waC st hc))
theorem c110 (st : AS V) (hc : Clean st) : Clean (f110 st) :=
  wexC _ (waC st hc)

/-- axioms().n_091.3 -/
noncomputable def f80 (st : AS V) : AS V := par3F (f110 st)
theorem l80 (st : AS V) (hc : Clean st) : Rn (.node 80) st (f80 st) :=
  R.seq (n := 80) rfl (l110 st hc) (par3L _ (c110 st hc))
theorem c80 (st : AS V) (hc : Clean st) : Clean (f80 st) :=
  par3C _ (c110 st hc)

/-- axioms().n_091.2 -/
noncomputable def f79 (st : AS V) : AS V := f80 (f109 st)
theorem l79 (st : AS V) (hc : Clean st) : Rn (.node 79) st (f79 st) :=
  R.seq (n := 79) rfl (l109 st hc) (l80 _ (c109 st hc))
theorem c79 (st : AS V) (hc : Clean st) : Clean (f79 st) :=
  c80 _ (c109 st hc)

/-- axioms().n_091.1 -/
noncomputable def f78 (st : AS V) : AS V := f79 (par3F st)
theorem l78 (st : AS V) (hc : Clean st) : Rn (.node 78) st (f78 st) :=
  R.seq (n := 78) rfl (par3L st hc) (l79 _ (par3C st hc))
theorem c78 (st : AS V) (hc : Clean st) : Clean (f78 st) :=
  c79 _ (par3C st hc)

/-- axioms().n_091.0 -/
noncomputable def f77 (st : AS V) : AS V := f78 (f107 st)
theorem l77 (st : AS V) (hc : Clean st) : Rn (.node 77) st (f77 st) :=
  R.seq (n := 77) rfl (l107 st hc) (l78 _ (c107 st hc))
theorem c77 (st : AS V) (hc : Clean st) : Clean (f77 st) :=
  c78 _ (c107 st hc)

/-- axioms().51.0 -/
noncomputable def f49 (st : AS V) : AS V := f103 (par2F st)
theorem l49 (st : AS V) (hc : Clean st) : Rn (.node 49) st (f49 st) :=
  R.seq (n := 49) rfl (par2L st hc) (l103 _ (par2C st hc))
theorem c49 (st : AS V) (hc : Clean st) : Clean (f49 st) :=
  c103 _ (par2C st hc)

/-- axioms().n_104.0 -/
noncomputable def f100 (st : AS V) : AS V := f107 (wexF st)
theorem l100 (st : AS V) (hc : Clean st) : Rn (.node 100) st (f100 st) :=
  R.seq (n := 100) rfl (wexL st hc) (l107 _ (wexC st hc))
theorem c100 (st : AS V) (hc : Clean st) : Clean (f100 st) :=
  c107 _ (wexC st hc)

/-- axioms().70 -/
noncomputable def f70 (st : AS V) : AS V := gateF (waF st)
theorem l70 (st : AS V) (hc : Clean st) : Rn (.node 70) st (f70 st) :=
  R.seq (n := 70) rfl (waL st hc) (l71 _ (waC st hc))
theorem c70 (st : AS V) (hc : Clean st) : Clean (f70 st) :=
  gateC _ (waC st hc)

/-- axioms().69 -/
noncomputable def f68 (st : AS V) : AS V := f70 (waF st)
theorem l68 (st : AS V) (hc : Clean st) : Rn (.node 68) st (f68 st) :=
  R.seq (n := 68) rfl (waL st hc) (l70 _ (waC st hc))
theorem c68 (st : AS V) (hc : Clean st) : Clean (f68 st) :=
  c70 _ (waC st hc)

/-- axioms().68 -/
noncomputable def f67 (st : AS V) : AS V := f68 (consF st)
theorem l67 (st : AS V) (hc : Clean st) : Rn (.node 67) st (f67 st) :=
  R.seq (n := 67) rfl (consL st hc) (l68 _ (consC st hc))
theorem c67 (st : AS V) (hc : Clean st) : Clean (f67 st) :=
  c68 _ (consC st hc)

/-- axioms().67 -/
noncomputable def f66 (st : AS V) : AS V := f67 (walF st)
theorem l66 (st : AS V) (hc : Clean st) : Rn (.node 66) st (f66 st) :=
  R.seq (n := 66) rfl (walL st hc) (l67 _ (walC st hc))
theorem c66 (st : AS V) (hc : Clean st) : Clean (f66 st) :=
  c67 _ (walC st hc)

/-- axioms().66 -/
noncomputable def f65 (st : AS V) : AS V := f66 (f108 st)
theorem l65 (st : AS V) (hc : Clean st) : Rn (.node 65) st (f65 st) :=
  R.seq (n := 65) rfl (l108 st hc) (l66 _ (c108 st hc))
theorem c65 (st : AS V) (hc : Clean st) : Clean (f65 st) :=
  c66 _ (c108 st hc)

/-- axioms().65 -/
noncomputable def f64 (st : AS V) : AS V := f65 (f84 st)
theorem l64 (st : AS V) (hc : Clean st) : Rn (.node 64) st (f64 st) :=
  R.seq (n := 64) rfl (l84 st hc) (l65 _ (c84 st hc))
theorem c64 (st : AS V) (hc : Clean st) : Clean (f64 st) :=
  c65 _ (c84 st hc)

/-- axioms().64 -/
noncomputable def f63 (st : AS V) : AS V := f64 (f109 st)
theorem l63 (st : AS V) (hc : Clean st) : Rn (.node 63) st (f63 st) :=
  R.seq (n := 63) rfl (l109 st hc) (l64 _ (c109 st hc))
theorem c63 (st : AS V) (hc : Clean st) : Clean (f63 st) :=
  c64 _ (c109 st hc)

/-- axioms().63 -/
noncomputable def f62 (st : AS V) : AS V := f63 (f93 st)
theorem l62 (st : AS V) (hc : Clean st) : Rn (.node 62) st (f62 st) :=
  R.seq (n := 62) rfl (l93 st hc) (l63 _ (c93 st hc))
theorem c62 (st : AS V) (hc : Clean st) : Clean (f62 st) :=
  c63 _ (c93 st hc)

/-- axioms().62 -/
noncomputable def f61 (st : AS V) : AS V := f62 (par1F st)
theorem l61 (st : AS V) (hc : Clean st) : Rn (.node 61) st (f61 st) :=
  R.seq (n := 61) rfl (par1L st hc) (l62 _ (par1C st hc))
theorem c61 (st : AS V) (hc : Clean st) : Clean (f61 st) :=
  c62 _ (par1C st hc)

/-- axioms().61 -/
noncomputable def f60 (st : AS V) : AS V := f61 (waF st)
theorem l60 (st : AS V) (hc : Clean st) : Rn (.node 60) st (f60 st) :=
  R.seq (n := 60) rfl (waL st hc) (l61 _ (waC st hc))
theorem c60 (st : AS V) (hc : Clean st) : Clean (f60 st) :=
  c61 _ (waC st hc)

/-- axioms().60 -/
noncomputable def f59 (st : AS V) : AS V := f60 (f110 st)
theorem l59 (st : AS V) (hc : Clean st) : Rn (.node 59) st (f59 st) :=
  R.seq (n := 59) rfl (l110 st hc) (l60 _ (c110 st hc))
theorem c59 (st : AS V) (hc : Clean st) : Clean (f59 st) :=
  c60 _ (c110 st hc)

/-- axioms().59 -/
noncomputable def f57 (st : AS V) : AS V := f59 (f100 st)
theorem l57 (st : AS V) (hc : Clean st) : Rn (.node 57) st (f57 st) :=
  R.seq (n := 57) rfl (l100 st hc) (l59 _ (c100 st hc))
theorem c57 (st : AS V) (hc : Clean st) : Clean (f57 st) :=
  c59 _ (c100 st hc)

/-- axioms().58 -/
noncomputable def f56 (st : AS V) : AS V := f57 (f112 st)
theorem l56 (st : AS V) (hc : Clean st) : Rn (.node 56) st (f56 st) :=
  R.seq (n := 56) rfl (l112 st hc) (l57 _ (c112 st hc))
theorem c56 (st : AS V) (hc : Clean st) : Clean (f56 st) :=
  c57 _ (c112 st hc)

/-- axioms().57 -/
noncomputable def f55 (st : AS V) : AS V := f56 (f98 st)
theorem l55 (st : AS V) (hc : Clean st) : Rn (.node 55) st (f55 st) :=
  R.seq (n := 55) rfl (l98 st hc) (l56 _ (c98 st hc))
theorem c55 (st : AS V) (hc : Clean st) : Clean (f55 st) :=
  c56 _ (c98 st hc)

/-- axioms().56 -/
noncomputable def f54 (st : AS V) : AS V := f55 (par2F st)
theorem l54 (st : AS V) (hc : Clean st) : Rn (.node 54) st (f54 st) :=
  R.seq (n := 54) rfl (par2L st hc) (l55 _ (par2C st hc))
theorem c54 (st : AS V) (hc : Clean st) : Clean (f54 st) :=
  c55 _ (par2C st hc)

/-- axioms().55 -/
noncomputable def f53 (st : AS V) : AS V := f54 (f107 st)
theorem l53 (st : AS V) (hc : Clean st) : Rn (.node 53) st (f53 st) :=
  R.seq (n := 53) rfl (l107 st hc) (l54 _ (c107 st hc))
theorem c53 (st : AS V) (hc : Clean st) : Clean (f53 st) :=
  c54 _ (c107 st hc)

/-- axioms().54 -/
noncomputable def f52 (st : AS V) : AS V := f53 (f100 st)
theorem l52 (st : AS V) (hc : Clean st) : Rn (.node 52) st (f52 st) :=
  R.seq (n := 52) rfl (l100 st hc) (l53 _ (c100 st hc))
theorem c52 (st : AS V) (hc : Clean st) : Clean (f52 st) :=
  c53 _ (c100 st hc)

/-- axioms().53 -/
noncomputable def f51 (st : AS V) : AS V := f52 (waF st)
theorem l51 (st : AS V) (hc : Clean st) : Rn (.node 51) st (f51 st) :=
  R.seq (n := 51) rfl (waL st hc) (l52 _ (waC st hc))
theorem c51 (st : AS V) (hc : Clean st) : Clean (f51 st) :=
  c52 _ (waC st hc)

/-- axioms().52 -/
noncomputable def f50 (st : AS V) : AS V := f51 (f98 st)
theorem l50 (st : AS V) (hc : Clean st) : Rn (.node 50) st (f50 st) :=
  R.seq (n := 50) rfl (l98 st hc) (l51 _ (c98 st hc))
theorem c50 (st : AS V) (hc : Clean st) : Clean (f50 st) :=
  c51 _ (c98 st hc)

/-- axioms().51 -/
noncomputable def f48 (st : AS V) : AS V := f50 (f49 st)
theorem l48 (st : AS V) (hc : Clean st) : Rn (.node 48) st (f48 st) :=
  R.seq (n := 48) rfl (l49 st hc) (l50 _ (c49 st hc))
theorem c48 (st : AS V) (hc : Clean st) : Clean (f48 st) :=
  c50 _ (c49 st hc)

/-- axioms().50 -/
noncomputable def f47 (st : AS V) : AS V := f48 (f92 st)
theorem l47 (st : AS V) (hc : Clean st) : Rn (.node 47) st (f47 st) :=
  R.seq (n := 47) rfl (l92 st hc) (l48 _ (c92 st hc))
theorem c47 (st : AS V) (hc : Clean st) : Clean (f47 st) :=
  c48 _ (c92 st hc)

/-- axioms().49 -/
noncomputable def f45 (st : AS V) : AS V := f47 (f77 st)
theorem l45 (st : AS V) (hc : Clean st) : Rn (.node 45) st (f45 st) :=
  R.seq (n := 45) rfl (l77 st hc) (l47 _ (c77 st hc))
theorem c45 (st : AS V) (hc : Clean st) : Clean (f45 st) :=
  c47 _ (c77 st hc)

/-- axioms().48 -/
noncomputable def f44 (st : AS V) : AS V := f45 (waF st)
theorem l44 (st : AS V) (hc : Clean st) : Rn (.node 44) st (f44 st) :=
  R.seq (n := 44) rfl (waL st hc) (l45 _ (waC st hc))
theorem c44 (st : AS V) (hc : Clean st) : Clean (f44 st) :=
  c45 _ (waC st hc)

/-- axioms().47 -/
noncomputable def f43 (st : AS V) : AS V := f44 (f97 st)
theorem l43 (st : AS V) (hc : Clean st) : Rn (.node 43) st (f43 st) :=
  R.seq (n := 43) rfl (l97 st hc) (l44 _ (c97 st hc))
theorem c43 (st : AS V) (hc : Clean st) : Clean (f43 st) :=
  c44 _ (c97 st hc)

/-- axioms().46 -/
noncomputable def f42 (st : AS V) : AS V := f43 (par2F st)
theorem l42 (st : AS V) (hc : Clean st) : Rn (.node 42) st (f42 st) :=
  R.seq (n := 42) rfl (par2L st hc) (l43 _ (par2C st hc))
theorem c42 (st : AS V) (hc : Clean st) : Clean (f42 st) :=
  c43 _ (par2C st hc)

/-- axioms().45 -/
noncomputable def f41 (st : AS V) : AS V := f42 (f106 st)
theorem l41 (st : AS V) (hc : Clean st) : Rn (.node 41) st (f41 st) :=
  R.seq (n := 41) rfl (l106 st hc) (l42 _ (c106 st hc))
theorem c41 (st : AS V) (hc : Clean st) : Clean (f41 st) :=
  c42 _ (c106 st hc)

/-- axioms().44 -/
noncomputable def f40 (st : AS V) : AS V := f41 (f111 st)
theorem l40 (st : AS V) (hc : Clean st) : Rn (.node 40) st (f40 st) :=
  R.seq (n := 40) rfl (l111 st hc) (l41 _ (c111 st hc))
theorem c40 (st : AS V) (hc : Clean st) : Clean (f40 st) :=
  c41 _ (c111 st hc)

/-- axioms().43 -/
noncomputable def f39 (st : AS V) : AS V := f40 (f77 st)
theorem l39 (st : AS V) (hc : Clean st) : Rn (.node 39) st (f39 st) :=
  R.seq (n := 39) rfl (l77 st hc) (l40 _ (c77 st hc))
theorem c39 (st : AS V) (hc : Clean st) : Clean (f39 st) :=
  c40 _ (c77 st hc)

/-- axioms().42 -/
noncomputable def f38 (st : AS V) : AS V := f39 (f98 st)
theorem l38 (st : AS V) (hc : Clean st) : Rn (.node 38) st (f38 st) :=
  R.seq (n := 38) rfl (l98 st hc) (l39 _ (c98 st hc))
theorem c38 (st : AS V) (hc : Clean st) : Clean (f38 st) :=
  c39 _ (c98 st hc)

/-- axioms().41 -/
noncomputable def f37 (st : AS V) : AS V := f38 (f97 st)
theorem l37 (st : AS V) (hc : Clean st) : Rn (.node 37) st (f37 st) :=
  R.seq (n := 37) rfl (l97 st hc) (l38 _ (c97 st hc))
theorem c37 (st : AS V) (hc : Clean st) : Clean (f37 st) :=
  c38 _ (c97 st hc)

/-- axioms().40 -/
noncomputable def f36 (st : AS V) : AS V := f37 (f93 st)
theorem l36 (st : AS V) (hc : Clean st) : Rn (.node 36) st (f36 st) :=
  R.seq (n := 36) rfl (l93 st hc) (l37 _ (c93 st hc))
theorem c36 (st : AS V) (hc : Clean st) : Clean (f36 st) :=
  c37 _ (c93 st hc)

/-- axioms().39 -/
noncomputable def f34 (st : AS V) : AS V := f36 (par3F st)
theorem l34 (st : AS V) (hc : Clean st) : Rn (.node 34) st (f34 st) :=
  R.seq (n := 34) rfl (par3L st hc) (l36 _ (par3C st hc))
theorem c34 (st : AS V) (hc : Clean st) : Clean (f34 st) :=
  c36 _ (par3C st hc)

/-- axioms().38 -/
noncomputable def f33 (st : AS V) : AS V := f34 (f103 st)
theorem l33 (st : AS V) (hc : Clean st) : Rn (.node 33) st (f33 st) :=
  R.seq (n := 33) rfl (l103 st hc) (l34 _ (c103 st hc))
theorem c33 (st : AS V) (hc : Clean st) : Clean (f33 st) :=
  c34 _ (c103 st hc)

/-- axioms().37 -/
noncomputable def f32 (st : AS V) : AS V := f33 (f92 st)
theorem l32 (st : AS V) (hc : Clean st) : Rn (.node 32) st (f32 st) :=
  R.seq (n := 32) rfl (l92 st hc) (l33 _ (c92 st hc))
theorem c32 (st : AS V) (hc : Clean st) : Clean (f32 st) :=
  c33 _ (c92 st hc)

/-- axioms().36 -/
noncomputable def f31 (st : AS V) : AS V := f32 (f105 st)
theorem l31 (st : AS V) (hc : Clean st) : Rn (.node 31) st (f31 st) :=
  R.seq (n := 31) rfl (l105 st hc) (l32 _ (c105 st hc))
theorem c31 (st : AS V) (hc : Clean st) : Clean (f31 st) :=
  c32 _ (c105 st hc)

/-- axioms().35 -/
noncomputable def f30 (st : AS V) : AS V := f31 (weqF st)
theorem l30 (st : AS V) (hc : Clean st) : Rn (.node 30) st (f30 st) :=
  R.seq (n := 30) rfl (weqL st hc) (l31 _ (weqC st hc))
theorem c30 (st : AS V) (hc : Clean st) : Clean (f30 st) :=
  c31 _ (weqC st hc)

/-- axioms().34 -/
noncomputable def f29 (st : AS V) : AS V := f30 (f90 st)
theorem l29 (st : AS V) (hc : Clean st) : Rn (.node 29) st (f29 st) :=
  R.seq (n := 29) rfl (l90 st hc) (l30 _ (c90 st hc))
theorem c29 (st : AS V) (hc : Clean st) : Clean (f29 st) :=
  c30 _ (c90 st hc)

/-- axioms().33 -/
noncomputable def f28 (st : AS V) : AS V := f29 (f96 st)
theorem l28 (st : AS V) (hc : Clean st) : Rn (.node 28) st (f28 st) :=
  R.seq (n := 28) rfl (l96 st hc) (l29 _ (c96 st hc))
theorem c28 (st : AS V) (hc : Clean st) : Clean (f28 st) :=
  c29 _ (c96 st hc)

/-- axioms().32 -/
noncomputable def f27 (st : AS V) : AS V := f28 (f95 st)
theorem l27 (st : AS V) (hc : Clean st) : Rn (.node 27) st (f27 st) :=
  R.seq (n := 27) rfl (l95 st hc) (l28 _ (c95 st hc))
theorem c27 (st : AS V) (hc : Clean st) : Clean (f27 st) :=
  c28 _ (c95 st hc)

/-- axioms().31 -/
noncomputable def f26 (st : AS V) : AS V := f27 (f107 st)
theorem l26 (st : AS V) (hc : Clean st) : Rn (.node 26) st (f26 st) :=
  R.seq (n := 26) rfl (l107 st hc) (l27 _ (c107 st hc))
theorem c26 (st : AS V) (hc : Clean st) : Clean (f26 st) :=
  c27 _ (c107 st hc)

/-- axioms().30 -/
noncomputable def f25 (st : AS V) : AS V := f26 (f81 st)
theorem l25 (st : AS V) (hc : Clean st) : Rn (.node 25) st (f25 st) :=
  R.seq (n := 25) rfl (l81 st hc) (l26 _ (c81 st hc))
theorem c25 (st : AS V) (hc : Clean st) : Clean (f25 st) :=
  c26 _ (c81 st hc)

/-- axioms().29 -/
noncomputable def f23 (st : AS V) : AS V := f25 (f106 st)
theorem l23 (st : AS V) (hc : Clean st) : Rn (.node 23) st (f23 st) :=
  R.seq (n := 23) rfl (l106 st hc) (l25 _ (c106 st hc))
theorem c23 (st : AS V) (hc : Clean st) : Clean (f23 st) :=
  c25 _ (c106 st hc)

/-- axioms().28 -/
noncomputable def f22 (st : AS V) : AS V := f23 (f84 st)
theorem l22 (st : AS V) (hc : Clean st) : Rn (.node 22) st (f22 st) :=
  R.seq (n := 22) rfl (l84 st hc) (l23 _ (c84 st hc))
theorem c22 (st : AS V) (hc : Clean st) : Clean (f22 st) :=
  c23 _ (c84 st hc)

/-- axioms().27 -/
noncomputable def f21 (st : AS V) : AS V := f22 (f96 st)
theorem l21 (st : AS V) (hc : Clean st) : Rn (.node 21) st (f21 st) :=
  R.seq (n := 21) rfl (l96 st hc) (l22 _ (c96 st hc))
theorem c21 (st : AS V) (hc : Clean st) : Clean (f21 st) :=
  c22 _ (c96 st hc)

/-- axioms().26 -/
noncomputable def f20 (st : AS V) : AS V := f21 (par2F st)
theorem l20 (st : AS V) (hc : Clean st) : Rn (.node 20) st (f20 st) :=
  R.seq (n := 20) rfl (par2L st hc) (l21 _ (par2C st hc))
theorem c20 (st : AS V) (hc : Clean st) : Clean (f20 st) :=
  c21 _ (par2C st hc)

/-- axioms().25 -/
noncomputable def f19 (st : AS V) : AS V := f20 (walF st)
theorem l19 (st : AS V) (hc : Clean st) : Rn (.node 19) st (f19 st) :=
  R.seq (n := 19) rfl (walL st hc) (l20 _ (walC st hc))
theorem c19 (st : AS V) (hc : Clean st) : Clean (f19 st) :=
  c20 _ (walC st hc)

/-- axioms().24 -/
noncomputable def f18 (st : AS V) : AS V := f19 (walF st)
theorem l18 (st : AS V) (hc : Clean st) : Rn (.node 18) st (f18 st) :=
  R.seq (n := 18) rfl (walL st hc) (l19 _ (walC st hc))
theorem c18 (st : AS V) (hc : Clean st) : Clean (f18 st) :=
  c19 _ (walC st hc)

/-- axioms().23 -/
noncomputable def f17 (st : AS V) : AS V := f18 (f81 st)
theorem l17 (st : AS V) (hc : Clean st) : Rn (.node 17) st (f17 st) :=
  R.seq (n := 17) rfl (l81 st hc) (l18 _ (c81 st hc))
theorem c17 (st : AS V) (hc : Clean st) : Clean (f17 st) :=
  c18 _ (c81 st hc)

/-- axioms().22 -/
noncomputable def f16 (st : AS V) : AS V := f17 (par1F st)
theorem l16 (st : AS V) (hc : Clean st) : Rn (.node 16) st (f16 st) :=
  R.seq (n := 16) rfl (par1L st hc) (l17 _ (par1C st hc))
theorem c16 (st : AS V) (hc : Clean st) : Clean (f16 st) :=
  c17 _ (par1C st hc)

/-- axioms().21 -/
noncomputable def f15 (st : AS V) : AS V := f16 (welF st)
theorem l15 (st : AS V) (hc : Clean st) : Rn (.node 15) st (f15 st) :=
  R.seq (n := 15) rfl (welL st hc) (l16 _ (welC st hc))
theorem c15 (st : AS V) (hc : Clean st) : Clean (f15 st) :=
  c16 _ (welC st hc)

/-- axioms().20 -/
noncomputable def f14 (st : AS V) : AS V := f15 (f87 st)
theorem l14 (st : AS V) (hc : Clean st) : Rn (.node 14) st (f14 st) :=
  R.seq (n := 14) rfl (l87 st hc) (l15 _ (c87 st hc))
theorem c14 (st : AS V) (hc : Clean st) : Clean (f14 st) :=
  c15 _ (c87 st hc)

/-- axioms().19 -/
noncomputable def f12 (st : AS V) : AS V := f14 (f105 st)
theorem l12 (st : AS V) (hc : Clean st) : Rn (.node 12) st (f12 st) :=
  R.seq (n := 12) rfl (l105 st hc) (l14 _ (c105 st hc))
theorem c12 (st : AS V) (hc : Clean st) : Clean (f12 st) :=
  c14 _ (c105 st hc)

/-- axioms().18 -/
noncomputable def f11 (st : AS V) : AS V := f12 (walF st)
theorem l11 (st : AS V) (hc : Clean st) : Rn (.node 11) st (f11 st) :=
  R.seq (n := 11) rfl (walL st hc) (l12 _ (walC st hc))
theorem c11 (st : AS V) (hc : Clean st) : Clean (f11 st) :=
  c12 _ (walC st hc)

/-- axioms().17 -/
noncomputable def f10 (st : AS V) : AS V := f11 (f90 st)
theorem l10 (st : AS V) (hc : Clean st) : Rn (.node 10) st (f10 st) :=
  R.seq (n := 10) rfl (l90 st hc) (l11 _ (c90 st hc))
theorem c10 (st : AS V) (hc : Clean st) : Clean (f10 st) :=
  c11 _ (c90 st hc)

/-- axioms().16 -/
noncomputable def f9 (st : AS V) : AS V := f10 (f108 st)
theorem l9 (st : AS V) (hc : Clean st) : Rn (.node 9) st (f9 st) :=
  R.seq (n := 9) rfl (l108 st hc) (l10 _ (c108 st hc))
theorem c9 (st : AS V) (hc : Clean st) : Clean (f9 st) :=
  c10 _ (c108 st hc)

/-- axioms().15 -/
noncomputable def f8 (st : AS V) : AS V := f9 (par1F st)
theorem l8 (st : AS V) (hc : Clean st) : Rn (.node 8) st (f8 st) :=
  R.seq (n := 8) rfl (par1L st hc) (l9 _ (par1C st hc))
theorem c8 (st : AS V) (hc : Clean st) : Clean (f8 st) :=
  c9 _ (par1C st hc)

/-- axioms().14 -/
noncomputable def f7 (st : AS V) : AS V := f8 (weqF st)
theorem l7 (st : AS V) (hc : Clean st) : Rn (.node 7) st (f7 st) :=
  R.seq (n := 7) rfl (weqL st hc) (l8 _ (weqC st hc))
theorem c7 (st : AS V) (hc : Clean st) : Clean (f7 st) :=
  c8 _ (weqC st hc)

/-- axioms().13 -/
noncomputable def f6 (st : AS V) : AS V := f7 (f87 st)
theorem l6 (st : AS V) (hc : Clean st) : Rn (.node 6) st (f6 st) :=
  R.seq (n := 6) rfl (l87 st hc) (l7 _ (c87 st hc))
theorem c6 (st : AS V) (hc : Clean st) : Clean (f6 st) :=
  c7 _ (c87 st hc)

/-- axioms().12 -/
noncomputable def f5 (st : AS V) : AS V := f6 (consF st)
theorem l5 (st : AS V) (hc : Clean st) : Rn (.node 5) st (f5 st) :=
  R.seq (n := 5) rfl (consL st hc) (l6 _ (consC st hc))
theorem c5 (st : AS V) (hc : Clean st) : Clean (f5 st) :=
  c6 _ (consC st hc)

/-- axioms().11 -/
noncomputable def f4 (st : AS V) : AS V := f5 (f104 st)
theorem l4 (st : AS V) (hc : Clean st) : Rn (.node 4) st (f4 st) :=
  R.seq (n := 4) rfl (l104 st hc) (l5 _ (c104 st hc))
theorem c4 (st : AS V) (hc : Clean st) : Clean (f4 st) :=
  c5 _ (c104 st hc)

/-- axioms().10 -/
noncomputable def f3 (st : AS V) : AS V := f4 (par2F st)
theorem l3 (st : AS V) (hc : Clean st) : Rn (.node 3) st (f3 st) :=
  R.seq (n := 3) rfl (par2L st hc) (l4 _ (par2C st hc))
theorem c3 (st : AS V) (hc : Clean st) : Clean (f3 st) :=
  c4 _ (par2C st hc)

/-- axioms().9 -/
noncomputable def f76 (st : AS V) : AS V := f3 (f104 st)
theorem l76 (st : AS V) (hc : Clean st) : Rn (.node 76) st (f76 st) :=
  R.seq (n := 76) rfl (l104 st hc) (l3 _ (c104 st hc))
theorem c76 (st : AS V) (hc : Clean st) : Clean (f76 st) :=
  c3 _ (c104 st hc)

/-- axioms().8 -/
noncomputable def f75 (st : AS V) : AS V := f76 (par1F st)
theorem l75 (st : AS V) (hc : Clean st) : Rn (.node 75) st (f75 st) :=
  R.seq (n := 75) rfl (par1L st hc) (l76 _ (par1C st hc))
theorem c75 (st : AS V) (hc : Clean st) : Clean (f75 st) :=
  c76 _ (par1C st hc)

/-- axioms().7 -/
noncomputable def f69 (st : AS V) : AS V := f75 (f161 st)
theorem l69 (st : AS V) (hc : Clean st) : Rn (.node 69) st (f69 st) :=
  R.seq (n := 69) rfl (l161 st hc) (l75 _ (c161 st hc))
theorem c69 (st : AS V) (hc : Clean st) : Clean (f69 st) :=
  c75 _ (c161 st hc)

/-- axioms().6 -/
noncomputable def f58 (st : AS V) : AS V := f69 (consF st)
theorem l58 (st : AS V) (hc : Clean st) : Rn (.node 58) st (f58 st) :=
  R.seq (n := 58) rfl (consL st hc) (l69 _ (consC st hc))
theorem c58 (st : AS V) (hc : Clean st) : Clean (f58 st) :=
  c69 _ (consC st hc)

/-- axioms().5: move the literal from scratch1 into topwff, then continue. -/
noncomputable def f46 (st : AS V) : AS V := f58 { st with tw := st.tw + st.s1, s1 := 0 }
theorem l46 (st : AS V) (h2 : st.s2 = 0) : Rn (.node 46) st (f46 st) :=
  R.seq (n := 46) rfl (loop208 st) (l58 _ ⟨rfl, h2⟩)
theorem c46 (st : AS V) (h2 : st.s2 = 0) : Clean (f46 st) := c58 _ ⟨rfl, h2⟩

/-- axioms().4: read the literal `u` into topwff. -/
noncomputable def f35 (st : AS V) : AS V := f46 { st with pl := (second st.pl), s1 := (first st.pl) }
theorem l35 (st : AS V) (hc : Clean st) : Rn (.node 35) st (f35 st) :=
  R.seq (n := 35) rfl (read108 st hc) (l46 _ hc.2)
theorem c35 (st : AS V) (hc : Clean st) : Clean (f35 st) := c46 _ hc.2

/-- axioms().3 -/
noncomputable def f24 (st : AS V) : AS V := f35 (pushF st)
theorem l24 (st : AS V) (hc : Clean st) : Rn (.node 24) st (f24 st) :=
  R.seq (n := 24) rfl (pushL st hc) (l35 _ (pushC st hc))
theorem c24 (st : AS V) (hc : Clean st) : Clean (f24 st) :=
  c35 _ (pushC st hc)

/-- axioms().2 -/
noncomputable def f13 (st : AS V) : AS V := f24 (par3F st)
theorem l13 (st : AS V) (hc : Clean st) : Rn (.node 13) st (f13 st) :=
  R.seq (n := 13) rfl (par3L st hc) (l24 _ (par3C st hc))
theorem c13 (st : AS V) (hc : Clean st) : Clean (f13 st) :=
  c24 _ (par3C st hc)

/-- axioms().1 -/
noncomputable def f2 (st : AS V) : AS V := f13 (readp2F st)
theorem l2 (st : AS V) (hc : Clean st) : Rn (.node 2) st (f2 st) :=
  R.seq (n := 2) rfl (readp2L st hc) (l13 _ (readp2C st hc))
theorem c2 (st : AS V) (hc : Clean st) : Clean (f2 st) :=
  c13 _ (readp2C st hc)

/-- axioms().0 -/
noncomputable def f1 (st : AS V) : AS V := f2 (f95 st)
theorem l1 (st : AS V) (hc : Clean st) : Rn (.node 1) st (f1 st) :=
  R.seq (n := 1) rfl (l95 st hc) (l2 _ (c95 st hc))
theorem c1 (st : AS V) (hc : Clean st) : Clean (f1 st) :=
  c2 _ (c95 st hc)

end SetTheory.BusyBeaver.ZFC.ArithmeticL2
