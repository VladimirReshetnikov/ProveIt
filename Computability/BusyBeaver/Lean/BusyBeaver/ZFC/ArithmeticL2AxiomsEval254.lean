import BusyBeaver.ZFC.ArithmeticL2Axioms254

set_option autoImplicit false

/-!
# Internal L2, part 5: closed forms of the `axioms()` nodes

The internal counterpart of `L2AxiomsEval254`, in every model of `IΣ₁`:
each closed form is checked against the definitions of `ArithmeticL2Axioms254`
bottom-up, so that `unP (P x y) = (x, y)` collapses at every step. Ported
mechanically from the external module (itself generated) by
`Research/ZFC/rotation240_pa/port_l2_eval.py`.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticL2

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor RMDag
open ArithmeticCode254 (wim wel wal weq)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


/-- axioms().n_121.0 -/
theorem e113 (st : AS V) : f113 st = ⟨st.np, st.p2, cantor st.p1 (cantor st.tw st.ws), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f113, par1F, par2F, first_cantor, second_cantor, zero_add]

/-- axioms().n_100.0 -/
theorem e95 (st : AS V) : f95 st = ⟨st.np, wal st.p1 st.p2, cantor st.tw st.ws, st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f95, e113, walF, first_cantor, second_cantor, zero_add]

/-- node_111.0 -/
theorem e161 (st : AS V) : f161 st = ⟨st.np, wim st.tw st.p1, st.ws, st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f161, par1F, consF, first_cantor, second_cantor, zero_add]

/-- axioms().n_112.0 -/
theorem e104 (st : AS V) : f104 st = ⟨st.np, wim st.tw st.ac, st.ws, st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f104, par3F, consF, first_cantor, second_cantor, zero_add]

/-- axioms().n_119.0 -/
theorem e111 (st : AS V) : f111 st = ⟨st.np, st.p1, cantor st.ac (cantor st.tw st.ws), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f111, par3F, par1F, first_cantor, second_cantor, zero_add]

/-- axioms().n_122.0 -/
theorem e114 (st : AS V) : f114 st = ⟨st.np, st.p2, cantor st.ac (cantor st.tw st.ws), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f114, par3F, par2F, first_cantor, second_cantor, zero_add]

/-- axioms().n_094.2 -/
theorem e89 (st : AS V) : f89 st = ⟨st.np, st.p2, cantor st.ac (cantor (weq (first st.ws) st.tw) (second st.ws)), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f89, weqF, e114, first_cantor, second_cantor, zero_add]

/-- axioms().n_094.1 -/
theorem e88 (st : AS V) : f88 st = ⟨st.np, st.p2, cantor st.ac (cantor (weq st.ac st.p1) (cantor st.tw st.ws)), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f88, e111, e89, first_cantor, second_cantor, zero_add]

/-- axioms().n_094.0 -/
theorem e87 (st : AS V) : f87 st = ⟨st.np, st.p2, cantor st.ac (cantor (weq st.ac st.p1) (cantor (wim (first st.ws) st.tw) (second st.ws))), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f87, consF, e88, first_cantor, second_cantor, zero_add]

/-- axioms().n_116.0 -/
theorem e108 (st : AS V) : f108 st = ⟨st.np, weq st.tw st.p2, st.ws, st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f108, par2F, weqF, first_cantor, second_cantor, zero_add]

/-- axioms().n_106.0 -/
theorem e102 (st : AS V) : f102 st = ⟨st.np, st.p2, cantor st.p1 (cantor st.p1 (cantor st.tw st.ws)), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f102, par1F, e113, first_cantor, second_cantor, zero_add]

/-- axioms().n_095.1 -/
theorem e91 (st : AS V) : f91 st = ⟨st.np, st.p2, cantor st.p1 (cantor st.p1 (cantor (wim (first st.ws) st.tw) (second st.ws))), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f91, consF, e102, first_cantor, second_cantor, zero_add]

/-- axioms().n_095.0 -/
theorem e90 (st : AS V) : f90 st = ⟨st.np, st.p2, cantor st.p1 (cantor st.p1 (cantor (wim (first (second st.ws)) (wim (first st.ws) st.tw)) (second (second st.ws)))), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f90, consF, e91, first_cantor, second_cantor, zero_add]

/-- axioms().n_113.0 -/
theorem e105 (st : AS V) : f105 st = ⟨st.np, st.p2, cantor (wex (first st.ws) st.tw) (second st.ws), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f105, wexF, par2F, first_cantor, second_cantor, zero_add]

/-- axioms().n_117.0 -/
theorem e109 (st : AS V) : f109 st = ⟨st.np, wel st.tw st.p2, st.ws, st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f109, par2F, welF, first_cantor, second_cantor, zero_add]

/-- axioms().n_105.0 -/
theorem e101 (st : AS V) : f101 st = ⟨st.np, st.p2, cantor st.p1 (cantor (wim (first st.ws) st.tw) (second st.ws)), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f101, consF, e113, first_cantor, second_cantor, zero_add]

/-- axioms().n_092.2 -/
theorem e83 (st : AS V) : f83 st = ⟨st.np, st.ac, cantor st.p2 (cantor st.p1 (cantor (wim (first st.ws) st.tw) (second st.ws))), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f83, e101, par3F, first_cantor, second_cantor, zero_add]

/-- axioms().n_092.1 -/
theorem e82 (st : AS V) : f82 st = ⟨st.np, st.ac, cantor st.p2 (cantor st.p1 (cantor (wim (first (second st.ws)) (wim (first st.ws) st.tw)) (second (second st.ws)))), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f82, consF, e83, first_cantor, second_cantor, zero_add]

/-- axioms().n_092.0 -/
theorem e81 (st : AS V) : f81 st = ⟨st.np, st.ac, cantor st.p2 (cantor st.p1 (cantor (wim (first (second st.ws)) (wim (first st.ws) (wel st.tw st.p2))) (second (second st.ws)))), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f81, e109, e82, first_cantor, second_cantor, zero_add]

/-- axioms().n_120.0 -/
theorem e112 (st : AS V) : f112 st = ⟨st.np, st.ac, cantor st.p1 (cantor st.tw st.ws), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f112, par1F, par3F, first_cantor, second_cantor, zero_add]

/-- axioms().n_101.0 -/
theorem e96 (st : AS V) : f96 st = ⟨st.np, wal st.p1 st.ac, cantor st.tw st.ws, st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f96, e112, walF, first_cantor, second_cantor, zero_add]

/-- axioms().n_093.2 -/
theorem e86 (st : AS V) : f86 st = ⟨st.np, st.p1, cantor st.ac (cantor (weq (first st.ws) st.tw) (second st.ws)), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f86, weqF, e111, first_cantor, second_cantor, zero_add]

/-- axioms().n_093.1 -/
theorem e85 (st : AS V) : f85 st = ⟨st.np, st.p1, cantor st.ac (cantor (weq st.p1 st.p2) (cantor (wim (first st.ws) st.tw) (second st.ws))), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f85, e101, e86, first_cantor, second_cantor, zero_add]

/-- axioms().n_093.0 -/
theorem e84 (st : AS V) : f84 st = ⟨st.np, st.p1, cantor st.ac (cantor (weq st.p1 st.p2) (cantor (wim (first (second st.ws)) (wal (first st.ws) st.tw)) (second (second st.ws)))), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f84, walF, e85, first_cantor, second_cantor, zero_add]

/-- axioms().n_114.0 -/
theorem e106 (st : AS V) : f106 st = ⟨st.np, st.ac, cantor (wel (first st.ws) st.tw) (second st.ws), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f106, welF, par3F, first_cantor, second_cantor, zero_add]

/-- axioms().n_115.0 -/
theorem e107 (st : AS V) : f107 st = ⟨st.np, wal (first (second st.ws)) (wim (first st.ws) st.tw), (second (second st.ws)), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f107, consF, walF, first_cantor, second_cantor, zero_add]

/-- axioms().n_096.0 -/
theorem e92 (st : AS V) : f92 st = ⟨st.np, wel st.p1 st.p2, cantor st.p1 (cantor st.tw st.ws), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f92, e102, welF, first_cantor, second_cantor, zero_add]

/-- axioms().n_107.0 -/
theorem e103 (st : AS V) : f103 st = ⟨st.np, st.ac, cantor st.p2 (cantor st.ac (cantor st.tw st.ws)), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f103, e114, par3F, first_cantor, second_cantor, zero_add]

/-- axioms().n_098.1 -/
theorem e94 (st : AS V) : f94 st = ⟨st.np, st.p1, cantor st.ac (cantor (wel (first st.ws) st.tw) (second st.ws)), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f94, e106, par1F, first_cantor, second_cantor, zero_add]

/-- axioms().n_098.0 -/
theorem e93 (st : AS V) : f93 st = ⟨st.np, st.p1, cantor st.ac (cantor (wel st.tw st.p2) st.ws), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f93, par2F, e94, first_cantor, second_cantor, zero_add]

/-- axioms().n_102.0 -/
theorem e97 (st : AS V) : f97 st = ⟨st.np, wal (first (second (second st.ws))) (wim (first (second st.ws)) (wel (first st.ws) st.tw)), (second (second (second st.ws))), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f97, welF, e107, first_cantor, second_cantor, zero_add]

/-- axioms().n_103.1 -/
theorem e99 (st : AS V) : f99 st = ⟨st.np, wel st.tw st.ac, st.ws, st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f99, par3F, welF, first_cantor, second_cantor, zero_add]

/-- axioms().n_103.0 -/
theorem e98 (st : AS V) : f98 st = ⟨st.np, wel st.p2 st.ac, cantor st.tw st.ws, st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f98, par2F, e99, first_cantor, second_cantor, zero_add]

/-- axioms().n_118.0 -/
theorem e110 (st : AS V) : f110 st = ⟨st.np, wex (first (second st.ws)) (wa (first st.ws) st.tw), (second (second st.ws)), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f110, waF, wexF, first_cantor, second_cantor, zero_add]

/-- axioms().n_091.3 -/
theorem e80 (st : AS V) : f80 st = ⟨st.np, st.ac, cantor (wex (first (second st.ws)) (wa (first st.ws) st.tw)) (second (second st.ws)), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f80, e110, par3F, first_cantor, second_cantor, zero_add]

/-- axioms().n_091.2 -/
theorem e79 (st : AS V) : f79 st = ⟨st.np, st.ac, cantor (wex (first (second st.ws)) (wa (first st.ws) (wel st.tw st.p2))) (second (second st.ws)), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f79, e109, e80, first_cantor, second_cantor, zero_add]

/-- axioms().n_091.1 -/
theorem e78 (st : AS V) : f78 st = ⟨st.np, st.ac, cantor (wex (first st.ws) (wa st.tw (wel st.ac st.p2))) (second st.ws), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f78, par3F, e79, first_cantor, second_cantor, zero_add]

/-- axioms().n_091.0 -/
theorem e77 (st : AS V) : f77 st = ⟨st.np, st.ac, cantor (wex (first (second (second st.ws))) (wa (wal (first (second st.ws)) (wim (first st.ws) st.tw)) (wel st.ac st.p2))) (second (second (second st.ws))), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f77, e107, e78, first_cantor, second_cantor, zero_add]

/-- axioms().51.0 -/
theorem e49 (st : AS V) : f49 st = ⟨st.np, st.ac, cantor st.p2 (cantor st.ac (cantor st.p2 (cantor st.tw st.ws))), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f49, par2F, e103, first_cantor, second_cantor, zero_add]

/-- axioms().n_104.0 -/
theorem e100 (st : AS V) : f100 st = ⟨st.np, wal (first (second (second st.ws))) (wim (first (second st.ws)) (wex (first st.ws) st.tw)), (second (second (second st.ws))), st.ac, st.p1, st.p2, st.s1, st.s2, st.pl⟩ := by
  simp only [f100, wexF, e107, first_cantor, second_cantor, zero_add]

/-- axioms().70 -/
theorem e70 (st : AS V) : f70 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (first st.ws) st.tw, (second st.ws), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f70, waF, gateF, first_cantor, second_cantor, zero_add]

/-- axioms().69 -/
theorem e68 (st : AS V) : f68 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (first (second st.ws)) (wa (first st.ws) st.tw), (second (second st.ws)), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f68, waF, e70, first_cantor, second_cantor, zero_add]

/-- axioms().68 -/
theorem e67 (st : AS V) : f67 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (first (second (second st.ws))) (wa (first (second st.ws)) (wim (first st.ws) st.tw)), (second (second (second st.ws))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f67, consF, e68, first_cantor, second_cantor, zero_add]

/-- axioms().67 -/
theorem e66 (st : AS V) : f66 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (first (second (second (second st.ws)))) (wa (first (second (second st.ws))) (wim (first (second st.ws)) (wal (first st.ws) st.tw))), (second (second (second (second st.ws)))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f66, walF, e67, first_cantor, second_cantor, zero_add]

/-- axioms().66 -/
theorem e65 (st : AS V) : f65 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (first (second (second (second st.ws)))) (wa (first (second (second st.ws))) (wim (first (second st.ws)) (wal (first st.ws) (weq st.tw st.p2)))), (second (second (second (second st.ws)))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f65, e108, e66, first_cantor, second_cantor, zero_add]

/-- axioms().65 -/
theorem e64 (st : AS V) : f64 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (first (second (second st.ws))) (wa (wim (first (second st.ws)) (wal (first st.ws) st.tw)) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second st.ws))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f64, e84, e65, first_cantor, second_cantor, zero_add]

/-- axioms().64 -/
theorem e63 (st : AS V) : f63 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (first (second (second st.ws))) (wa (wim (first (second st.ws)) (wal (first st.ws) (wel st.tw st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second st.ws))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f63, e109, e64, first_cantor, second_cantor, zero_add]

/-- axioms().63 -/
theorem e62 (st : AS V) : f62 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (first st.ws) (wa (wim (wel st.tw st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second st.ws), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f62, e93, e63, first_cantor, second_cantor, zero_add]

/-- axioms().62 -/
theorem e61 (st : AS V) : f61 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa st.tw (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), st.ws, 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f61, par1F, e62, first_cantor, second_cantor, zero_add]

/-- axioms().61 -/
theorem e60 (st : AS V) : f60 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (first st.ws) st.tw) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second st.ws), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f60, waF, e61, first_cantor, second_cantor, zero_add]

/-- axioms().60 -/
theorem e59 (st : AS V) : f59 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (first (second (second st.ws))) (wex (first (second st.ws)) (wa (first st.ws) st.tw))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second st.ws))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f59, e110, e60, first_cantor, second_cantor, zero_add]

/-- axioms().59 -/
theorem e57 (st : AS V) : f57 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (first (second (second (second (second (second st.ws)))))) (wex (first (second (second (second (second st.ws))))) (wa (first (second (second (second st.ws)))) (wal (first (second (second st.ws))) (wim (first (second st.ws)) (wex (first st.ws) st.tw)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second (second (second st.ws)))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f57, e100, e59, first_cantor, second_cantor, zero_add]

/-- axioms().58 -/
theorem e56 (st : AS V) : f56 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (first (second (second (second st.ws)))) (wex (first (second (second st.ws))) (wa (first (second st.ws)) (wal (first st.ws) (wim st.tw (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second st.ws)))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f56, e112, e57, first_cantor, second_cantor, zero_add]

/-- axioms().57 -/
theorem e55 (st : AS V) : f55 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (first (second (second st.ws))) (wex (first (second st.ws)) (wa (first st.ws) (wal st.tw (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second st.ws))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f55, e98, e56, first_cantor, second_cantor, zero_add]

/-- axioms().56 -/
theorem e54 (st : AS V) : f54 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (first (second st.ws)) (wex (first st.ws) (wa st.tw (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second st.ws)), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f54, par2F, e55, first_cantor, second_cantor, zero_add]

/-- axioms().55 -/
theorem e53 (st : AS V) : f53 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (first (second (second (second st.ws)))) (wex (first (second (second st.ws))) (wa (wal (first (second st.ws)) (wim (first st.ws) st.tw)) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second st.ws)))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f53, e107, e54, first_cantor, second_cantor, zero_add]

/-- axioms().54 -/
theorem e52 (st : AS V) : f52 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (first (second (second (second (second (second (second st.ws))))))) (wex (first (second (second (second (second (second st.ws)))))) (wa (wal (first (second (second (second (second st.ws))))) (wim (first (second (second (second st.ws)))) (wal (first (second (second st.ws))) (wim (first (second st.ws)) (wex (first st.ws) st.tw))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second (second (second (second st.ws))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f52, e100, e53, first_cantor, second_cantor, zero_add]

/-- axioms().53 -/
theorem e51 (st : AS V) : f51 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (first (second (second (second (second (second (second (second st.ws)))))))) (wex (first (second (second (second (second (second (second st.ws))))))) (wa (wal (first (second (second (second (second (second st.ws)))))) (wim (first (second (second (second (second st.ws))))) (wal (first (second (second (second st.ws)))) (wim (first (second (second st.ws))) (wex (first (second st.ws)) (wa (first st.ws) st.tw)))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second (second (second (second (second st.ws)))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f51, waF, e52, first_cantor, second_cantor, zero_add]

/-- axioms().52 -/
theorem e50 (st : AS V) : f50 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (first (second (second (second (second (second (second st.ws))))))) (wex (first (second (second (second (second (second st.ws)))))) (wa (wal (first (second (second (second (second st.ws))))) (wim (first (second (second (second st.ws)))) (wal (first (second (second st.ws))) (wim (first (second st.ws)) (wex (first st.ws) (wa st.tw (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second (second (second (second st.ws))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f50, e98, e51, first_cantor, second_cantor, zero_add]

/-- axioms().51 -/
theorem e48 (st : AS V) : f48 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (first (second (second st.ws))) (wex (first (second st.ws)) (wa (wal (first st.ws) (wim st.tw (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second st.ws))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f48, e49, e50, first_cantor, second_cantor, zero_add]

/-- axioms().50 -/
theorem e47 (st : AS V) : f47 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (first st.ws) (wex st.tw (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second st.ws), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f47, e92, e48, first_cantor, second_cantor, zero_add]

/-- axioms().49 -/
theorem e45 (st : AS V) : f45 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex (first (second (second st.ws))) (wa (wal (first (second st.ws)) (wim (first st.ws) st.tw)) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second st.ws))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f45, e77, e47, first_cantor, second_cantor, zero_add]

/-- axioms().48 -/
theorem e44 (st : AS V) : f44 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex (first (second (second (second st.ws)))) (wa (wal (first (second (second st.ws))) (wim (first (second st.ws)) (wa (first st.ws) st.tw))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second st.ws)))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f44, waF, e45, first_cantor, second_cantor, zero_add]

/-- axioms().47 -/
theorem e43 (st : AS V) : f43 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex (first (second (second (second (second (second (second st.ws))))))) (wa (wal (first (second (second (second (second (second st.ws)))))) (wim (first (second (second (second (second st.ws))))) (wa (first (second (second (second st.ws)))) (wal (first (second (second st.ws))) (wim (first (second st.ws)) (wel (first st.ws) st.tw)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second (second (second (second st.ws))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f43, e97, e44, first_cantor, second_cantor, zero_add]

/-- axioms().46 -/
theorem e42 (st : AS V) : f42 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex (first (second (second (second (second (second st.ws)))))) (wa (wal (first (second (second (second (second st.ws))))) (wim (first (second (second (second st.ws)))) (wa (first (second (second st.ws))) (wal (first (second st.ws)) (wim (first st.ws) (wel st.tw st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second (second (second st.ws)))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f42, par2F, e43, first_cantor, second_cantor, zero_add]

/-- axioms().45 -/
theorem e41 (st : AS V) : f41 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex (first (second (second (second (second (second st.ws)))))) (wa (wal (first (second (second (second (second st.ws))))) (wim (first (second (second (second st.ws)))) (wa (first (second (second st.ws))) (wal (first (second st.ws)) (wim (wel (first st.ws) st.tw) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second (second (second st.ws)))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f41, e106, e42, first_cantor, second_cantor, zero_add]

/-- axioms().44 -/
theorem e40 (st : AS V) : f40 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex (first (second (second (second st.ws)))) (wa (wal (first (second (second st.ws))) (wim (first (second st.ws)) (wa (first st.ws) (wal st.tw (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second st.ws)))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f40, e111, e41, first_cantor, second_cantor, zero_add]

/-- axioms().43 -/
theorem e39 (st : AS V) : f39 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex (first (second (second (second (second (second st.ws)))))) (wa (wal (first (second (second (second (second st.ws))))) (wim (first (second (second (second st.ws)))) (wa (wex (first (second (second st.ws))) (wa (wal (first (second st.ws)) (wim (first st.ws) st.tw)) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second (second (second st.ws)))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f39, e77, e40, first_cantor, second_cantor, zero_add]

/-- axioms().42 -/
theorem e38 (st : AS V) : f38 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex (first (second (second (second (second st.ws))))) (wa (wal (first (second (second (second st.ws)))) (wim (first (second (second st.ws))) (wa (wex (first (second st.ws)) (wa (wal (first st.ws) (wim st.tw (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second (second st.ws))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f38, e98, e39, first_cantor, second_cantor, zero_add]

/-- axioms().41 -/
theorem e37 (st : AS V) : f37 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex (first (second (second (second (second (second (second (second st.ws)))))))) (wa (wal (first (second (second (second (second (second (second st.ws))))))) (wim (first (second (second (second (second (second st.ws)))))) (wa (wex (first (second (second (second (second st.ws))))) (wa (wal (first (second (second (second st.ws)))) (wim (wal (first (second (second st.ws))) (wim (first (second st.ws)) (wel (first st.ws) st.tw))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second (second (second (second (second st.ws)))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f37, e97, e38, first_cantor, second_cantor, zero_add]

/-- axioms().40 -/
theorem e36 (st : AS V) : f36 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex (first (second (second (second (second (second st.ws)))))) (wa (wal (first (second (second (second (second st.ws))))) (wim (first (second (second (second st.ws)))) (wa (wex (first (second (second st.ws))) (wa (wal (first (second st.ws)) (wim (wal (first st.ws) (wim (wel st.tw st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second (second (second st.ws)))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f36, e93, e37, first_cantor, second_cantor, zero_add]

/-- axioms().39 -/
theorem e34 (st : AS V) : f34 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex (first (second (second (second (second st.ws))))) (wa (wal (first (second (second (second st.ws)))) (wim (first (second (second st.ws))) (wa (wex (first (second st.ws)) (wa (wal (first st.ws) (wim (wal st.tw (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second (second (second (second st.ws))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f34, par3F, e36, first_cantor, second_cantor, zero_add]

/-- axioms().38 -/
theorem e33 (st : AS V) : f33 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex (first (second st.ws)) (wa (wal (first st.ws) (wim st.tw (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), (second (second st.ws)), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f33, e103, e34, first_cantor, second_cantor, zero_add]

/-- axioms().37 -/
theorem e32 (st : AS V) : f32 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.tw (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), st.ws, 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f32, e92, e33, first_cantor, second_cantor, zero_add]

/-- axioms().36 -/
theorem e31 (st : AS V) : f31 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex (first st.ws) st.tw) (second st.ws), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f31, e105, e32, first_cantor, second_cantor, zero_add]

/-- axioms().35 -/
theorem e30 (st : AS V) : f30 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex (first (second st.ws)) (weq (first st.ws) st.tw)) (second (second st.ws)), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f30, weqF, e31, first_cantor, second_cantor, zero_add]

/-- axioms().34 -/
theorem e29 (st : AS V) : f29 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (first (second st.ws)) (wim (first st.ws) st.tw)) (second (second st.ws))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f29, e90, e30, first_cantor, second_cantor, zero_add]

/-- axioms().33 -/
theorem e28 (st : AS V) : f28 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (first st.ws) (wim st.tw (wal st.p1 st.ac))) (second st.ws)), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f28, e96, e29, first_cantor, second_cantor, zero_add]

/-- axioms().32 -/
theorem e27 (st : AS V) : f27 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim st.tw (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) st.ws), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f27, e95, e28, first_cantor, second_cantor, zero_add]

/-- axioms().31 -/
theorem e26 (st : AS V) : f26 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal (first (second st.ws)) (wim (first st.ws) st.tw)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (second (second st.ws))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f26, e107, e27, first_cantor, second_cantor, zero_add]

/-- axioms().30 -/
theorem e25 (st : AS V) : f25 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (first (second st.ws)) (wim (first st.ws) (wel st.tw st.p2))) (second (second st.ws)))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f25, e81, e26, first_cantor, second_cantor, zero_add]

/-- axioms().29 -/
theorem e23 (st : AS V) : f23 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (first (second st.ws)) (wim (wel (first st.ws) st.tw) (wel st.ac st.p2))) (second (second st.ws)))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f23, e106, e25, first_cantor, second_cantor, zero_add]

/-- axioms().28 -/
theorem e22 (st : AS V) : f22 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (first (second st.ws)) (wal (first st.ws) st.tw)) (second (second st.ws))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f22, e84, e23, first_cantor, second_cantor, zero_add]

/-- axioms().27 -/
theorem e21 (st : AS V) : f21 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (first st.ws) (wal st.tw (wal st.p1 st.ac))) (second st.ws)))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f21, e96, e22, first_cantor, second_cantor, zero_add]

/-- axioms().26 -/
theorem e20 (st : AS V) : f20 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim st.tw (wal st.p2 (wal st.p1 st.ac))) st.ws))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f20, par2F, e21, first_cantor, second_cantor, zero_add]

/-- axioms().25 -/
theorem e19 (st : AS V) : f19 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal (first st.ws) st.tw) (wal st.p2 (wal st.p1 st.ac))) (second st.ws)))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f19, walF, e20, first_cantor, second_cantor, zero_add]

/-- axioms().24 -/
theorem e18 (st : AS V) : f18 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal (first (second st.ws)) (wal (first st.ws) st.tw)) (wal st.p2 (wal st.p1 st.ac))) (second (second st.ws))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f18, walF, e19, first_cantor, second_cantor, zero_add]

/-- axioms().23 -/
theorem e17 (st : AS V) : f17 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (first (second st.ws)) (wim (first st.ws) (wel st.tw st.p2))) (second (second st.ws)))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f17, e81, e18, first_cantor, second_cantor, zero_add]

/-- axioms().22 -/
theorem e16 (st : AS V) : f16 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (first st.ws) (wim st.tw (wel st.p1 st.p2))) (second st.ws))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f16, par1F, e17, first_cantor, second_cantor, zero_add]

/-- axioms().21 -/
theorem e15 (st : AS V) : f15 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (first (second st.ws)) (wim (wel (first st.ws) st.tw) (wel st.p1 st.p2))) (second (second st.ws)))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f15, welF, e16, first_cantor, second_cantor, zero_add]

/-- axioms().20 -/
theorem e14 (st : AS V) : f14 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (first st.ws) st.tw) (second st.ws)))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f14, e87, e15, first_cantor, second_cantor, zero_add]

/-- axioms().19 -/
theorem e12 (st : AS V) : f12 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex (first st.ws) st.tw) st.p2) (second st.ws)))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f12, e105, e14, first_cantor, second_cantor, zero_add]

/-- axioms().18 -/
theorem e11 (st : AS V) : f11 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex (first (second st.ws)) (wal (first st.ws) st.tw)) st.p2) (second (second st.ws))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f11, walF, e12, first_cantor, second_cantor, zero_add]

/-- axioms().17 -/
theorem e10 (st : AS V) : f10 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (first (second st.ws)) (wim (first st.ws) st.tw)) (second (second st.ws)))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f10, e90, e11, first_cantor, second_cantor, zero_add]

/-- axioms().16 -/
theorem e9 (st : AS V) : f9 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (first (second st.ws)) (wim (first st.ws) (weq st.tw st.p2))) (second (second st.ws)))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f9, e108, e10, first_cantor, second_cantor, zero_add]

/-- axioms().15 -/
theorem e8 (st : AS V) : f8 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (first st.ws) (wim st.tw (weq st.p1 st.p2))) (second st.ws))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f8, par1F, e9, first_cantor, second_cantor, zero_add]

/-- axioms().14 -/
theorem e7 (st : AS V) : f7 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (first (second st.ws)) (wim (weq (first st.ws) st.tw) (weq st.p1 st.p2))) (second (second st.ws)))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f7, weqF, e8, first_cantor, second_cantor, zero_add]

/-- axioms().13 -/
theorem e6 (st : AS V) : f6 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (weq st.ac st.p1) (wim (weq st.ac st.p2) (weq st.p1 st.p2))) (cantor (wim (first st.ws) st.tw) (second st.ws)))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f6, e87, e7, first_cantor, second_cantor, zero_add]

/-- axioms().12 -/
theorem e5 (st : AS V) : f5 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (weq st.ac st.p1) (wim (weq st.ac st.p2) (weq st.p1 st.p2))) (cantor (wim (first (second st.ws)) (wim (first st.ws) st.tw)) (second (second st.ws))))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f5, consF, e6, first_cantor, second_cantor, zero_add]

/-- axioms().11 -/
theorem e4 (st : AS V) : f4 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (weq st.ac st.p1) (wim (weq st.ac st.p2) (weq st.p1 st.p2))) (cantor (wim (first (second st.ws)) (wim (first st.ws) (wim st.tw st.ac))) (second (second st.ws))))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f4, e104, e5, first_cantor, second_cantor, zero_add]

/-- axioms().10 -/
theorem e3 (st : AS V) : f3 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (weq st.ac st.p1) (wim (weq st.ac st.p2) (weq st.p1 st.p2))) (cantor (wim (first st.ws) (wim st.tw (wim st.p2 st.ac))) (second st.ws)))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f3, par2F, e4, first_cantor, second_cantor, zero_add]

/-- axioms().9 -/
theorem e76 (st : AS V) : f76 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (weq st.ac st.p1) (wim (weq st.ac st.p2) (weq st.p1 st.p2))) (cantor (wim (first st.ws) (wim (wim st.tw st.ac) (wim st.p2 st.ac))) (second st.ws)))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f76, e104, e3, first_cantor, second_cantor, zero_add]

/-- axioms().8 -/
theorem e75 (st : AS V) : f75 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (weq st.ac st.p1) (wim (weq st.ac st.p2) (weq st.p1 st.p2))) (cantor (wim st.tw (wim (wim st.p1 st.ac) (wim st.p2 st.ac))) st.ws))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f75, par1F, e76, first_cantor, second_cantor, zero_add]

/-- axioms().7 -/
theorem e69 (st : AS V) : f69 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (weq st.ac st.p1) (wim (weq st.ac st.p2) (weq st.p1 st.p2))) (cantor (wim (wim st.tw st.p1) (wim (wim st.p1 st.ac) (wim st.p2 st.ac))) st.ws))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f69, e161, e75, first_cantor, second_cantor, zero_add]

/-- axioms().6 -/
theorem e58 (st : AS V) : f58 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (weq st.ac st.p1) (wim (weq st.ac st.p2) (weq st.p1 st.p2))) (cantor (wim (wim (wim (first st.ws) st.tw) st.p1) (wim (wim st.p1 st.ac) (wim st.p2 st.ac))) (second st.ws)))))))), 0, 0, 0, st.s1, st.s2, st.pl⟩ := by
  simp only [f58, consF, e69, first_cantor, second_cantor, zero_add]

/-- axioms().4 -/
theorem e35 (st : AS V) : f35 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (weq st.ac st.p1) (wim (weq st.ac st.p2) (weq st.p1 st.p2))) (cantor (wim (wim (wim (first st.ws) (st.tw + (first st.pl))) st.p1) (wim (wim st.p1 st.ac) (wim st.p2 st.ac))) (second st.ws)))))))), 0, 0, 0, 0, st.s2, (second st.pl)⟩ := by
  simp only [f35, f46, e58, first_cantor, second_cantor, zero_add]

/-- axioms().3 -/
theorem e24 (st : AS V) : f24 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (weq st.ac st.p1) (wim (weq st.ac st.p2) (weq st.p1 st.p2))) (cantor (wim (wim (wim st.tw (first st.pl)) st.p1) (wim (wim st.p1 st.ac) (wim st.p2 st.ac))) st.ws))))))), 0, 0, 0, 0, st.s2, (second st.pl)⟩ := by
  simp only [f24, pushF, e35, first_cantor, second_cantor, zero_add]

/-- axioms().2 -/
theorem e13 (st : AS V) : f13 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else wa (wa (wex st.p2 (wa (wal st.p1 (wim (wel st.p1 st.p2) (wa (wex st.ac (wa (wal st.p2 (wim (wal st.ac (wim (wel st.ac st.p2) (wel st.ac st.p1))) (wel st.p2 st.ac))) (wel st.ac st.p2))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac st.p2)))))) (wel st.ac st.p2))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 st.p2) (wal st.p2 (wim st.ac (wex st.p2 (wa st.ac (wel st.p2 st.ac))))))) (wal st.p2 (wim (wel st.p2 st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 st.p2) (wal st.ac (wel st.p1 st.p2))) (wim (weq st.p1 st.p2) (wal st.ac (weq st.p1 st.p2)))), cantor (wex st.p1 (weq st.p1 st.p2)) (cantor (wim (wal st.p1 (wim st.p2 st.ac)) (wim (wal st.p1 st.p2) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 st.p2) (wim (wel st.ac st.p1) (wel st.ac st.p2))) (cantor (wim (wal st.p1 (wal st.p2 st.ac)) (wal st.p2 (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac st.p2) (wel st.p1 st.p2))) (cantor (wim (wex st.p1 (wal st.p1 st.p2)) st.p2) (cantor (wim (weq st.ac st.p1) (wim (weq st.ac st.p2) (weq st.p1 st.p2))) (cantor (wim (wim (wim st.ac (first st.pl)) st.p1) (wim (wim st.p1 st.ac) (wim st.p2 st.ac))) (cantor st.tw st.ws)))))))), 0, 0, 0, 0, st.s2, (second st.pl)⟩ := by
  simp only [f13, par3F, e24, first_cantor, second_cantor, zero_add]

/-- axioms().1 -/
theorem e2 (st : AS V) : f2 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 + (first st.pl) then 0 else wa (wa (wex (st.p2 + (first st.pl)) (wa (wal st.p1 (wim (wel st.p1 (st.p2 + (first st.pl))) (wa (wex st.ac (wa (wal (st.p2 + (first st.pl)) (wim (wal st.ac (wim (wel st.ac (st.p2 + (first st.pl))) (wel st.ac st.p1))) (wel (st.p2 + (first st.pl)) st.ac))) (wel st.ac (st.p2 + (first st.pl))))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac (st.p2 + (first st.pl)))))))) (wel st.ac (st.p2 + (first st.pl))))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 (st.p2 + (first st.pl))) (wal (st.p2 + (first st.pl)) (wim st.ac (wex (st.p2 + (first st.pl)) (wa st.ac (wel (st.p2 + (first st.pl)) st.ac))))))) (wal (st.p2 + (first st.pl)) (wim (wel (st.p2 + (first st.pl)) st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 (st.p2 + (first st.pl))) (wal st.ac (wel st.p1 (st.p2 + (first st.pl))))) (wim (weq st.p1 (st.p2 + (first st.pl))) (wal st.ac (weq st.p1 (st.p2 + (first st.pl)))))), cantor (wex st.p1 (weq st.p1 (st.p2 + (first st.pl)))) (cantor (wim (wal st.p1 (wim (st.p2 + (first st.pl)) st.ac)) (wim (wal st.p1 (st.p2 + (first st.pl))) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 (st.p2 + (first st.pl))) (wim (wel st.ac st.p1) (wel st.ac (st.p2 + (first st.pl))))) (cantor (wim (wal st.p1 (wal (st.p2 + (first st.pl)) st.ac)) (wal (st.p2 + (first st.pl)) (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac (st.p2 + (first st.pl))) (wel st.p1 (st.p2 + (first st.pl))))) (cantor (wim (wex st.p1 (wal st.p1 (st.p2 + (first st.pl)))) (st.p2 + (first st.pl))) (cantor (wim (weq st.ac st.p1) (wim (weq st.ac (st.p2 + (first st.pl))) (weq st.p1 (st.p2 + (first st.pl))))) (cantor (wim (wim (wim st.ac (first (second st.pl))) st.p1) (wim (wim st.p1 st.ac) (wim (st.p2 + (first st.pl)) st.ac))) (cantor st.tw st.ws)))))))), 0, 0, 0, 0, st.s2, (second (second st.pl))⟩ := by
  simp only [f2, readp2F, e13, first_cantor, second_cantor, zero_add]

/-- axioms().0 -/
theorem e1 (st : AS V) : f1 st = ⟨st.np, if st.ac = st.p1 ∨ st.ac = st.p2 + (first st.pl) then 0 else wa (wa (wex (st.p2 + (first st.pl)) (wa (wal st.p1 (wim (wel st.p1 (st.p2 + (first st.pl))) (wa (wex st.ac (wa (wal (st.p2 + (first st.pl)) (wim (wal st.ac (wim (wel st.ac (st.p2 + (first st.pl))) (wel st.ac st.p1))) (wel (st.p2 + (first st.pl)) st.ac))) (wel st.ac (st.p2 + (first st.pl))))) (wal st.ac (wim (wel st.ac st.p1) (wel st.ac (st.p2 + (first st.pl)))))))) (wel st.ac (st.p2 + (first st.pl))))) (wex st.ac (wa (wal st.p1 (wim (wel st.p1 (st.p2 + (first st.pl))) (wal (st.p2 + (first st.pl)) (wim st.ac (wex (st.p2 + (first st.pl)) (wa st.ac (wel (st.p2 + (first st.pl)) st.ac))))))) (wal (st.p2 + (first st.pl)) (wim (wel (st.p2 + (first st.pl)) st.ac) (wex st.p1 st.ac)))))) (wa (wim (wel st.p1 (st.p2 + (first st.pl))) (wal st.ac (wel st.p1 (st.p2 + (first st.pl))))) (wim (weq st.p1 (st.p2 + (first st.pl))) (wal st.ac (weq st.p1 (st.p2 + (first st.pl)))))), cantor (wex st.p1 (weq st.p1 (st.p2 + (first st.pl)))) (cantor (wim (wal st.p1 (wim (st.p2 + (first st.pl)) st.ac)) (wim (wal st.p1 (st.p2 + (first st.pl))) (wal st.p1 st.ac))) (cantor (wim (weq st.p1 (st.p2 + (first st.pl))) (wim (wel st.ac st.p1) (wel st.ac (st.p2 + (first st.pl))))) (cantor (wim (wal st.p1 (wal (st.p2 + (first st.pl)) st.ac)) (wal (st.p2 + (first st.pl)) (wal st.p1 st.ac))) (cantor (wim (weq st.ac st.p1) (wim (wel st.ac (st.p2 + (first st.pl))) (wel st.p1 (st.p2 + (first st.pl))))) (cantor (wim (wex st.p1 (wal st.p1 (st.p2 + (first st.pl)))) (st.p2 + (first st.pl))) (cantor (wim (weq st.ac st.p1) (wim (weq st.ac (st.p2 + (first st.pl))) (weq st.p1 (st.p2 + (first st.pl))))) (cantor (wim (wim (wim st.ac (first (second st.pl))) st.p1) (wim (wim st.p1 st.ac) (wim (st.p2 + (first st.pl)) st.ac))) (cantor (wal st.p1 st.p2) (cantor st.tw st.ws))))))))), 0, 0, 0, 0, st.s2, (second (second st.pl))⟩ := by
  simp only [f1, e95, e2, first_cantor, second_cantor, zero_add]

end SetTheory.BusyBeaver.ZFC.ArithmeticL2
