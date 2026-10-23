import BusyBeaver.ZFC.AXWord
import BusyBeaver.ZFC.Enum254

/-!
The native AX routine as a checked expression of shared register macros.
The literal expression names only semantic macros; `axExpr_checked` binds its
complete shape to the program. The shared structural proof supplies its run.
-/

namespace SetTheory.BusyBeaver.ZFC.L2

open RMDag Dag254 Code254 AXWord

attribute [local irreducible] Code254.P

set_option maxRecDepth 4096

def axExpr : AXExpr :=
  (.seq
    (.seq (.prefix .par1 (.atom .par2)) (.atom .wal))
    (.prefix .readp2
      (.prefix .par3
        (.prefix .push
          (.prefix .readwff
            (.prefix .cons
            (.seq
            (.prefix .par1 (.atom .cons))
            (.prefix .par1
            (.seq
            (.prefix .par3 (.atom .cons))
            (.prefix .par2
            (.seq
            (.prefix .par3 (.atom .cons))
            (.prefix .cons
            (.seq
            (.prefix .cons
            (.seq (.prefix .par3 (.atom .par1)) (.prefix .weq (.prefix .par3 (.atom .par2)))))
            (.prefix .weq
            (.prefix .par1
            (.seq
            (.prefix .par2 (.atom .weq))
            (.seq
            (.prefix .cons (.prefix .cons (.prefix .par1 (.prefix .par1 (.atom .par2)))))
            (.prefix .wal
            (.seq
            (.prefix .wex (.atom .par2))
            (.seq
            (.prefix .cons
            (.seq (.prefix .par3 (.atom .par1)) (.prefix .weq (.prefix .par3 (.atom .par2)))))
            (.prefix .wel
            (.prefix .par1
            (.seq
            (.seq
            (.prefix .par2 (.atom .wel))
            (.prefix .cons (.seq (.prefix .cons (.prefix .par1 (.atom .par2))) (.atom .par3))))
            (.prefix .wal
            (.prefix .wal
            (.prefix .par2
            (.seq
            (.seq (.prefix .par1 (.atom .par3)) (.atom .wal))
            (.seq
            (.prefix .wal
            (.seq
            (.prefix .cons (.prefix .par1 (.atom .par2)))
            (.prefix .weq (.prefix .par3 (.atom .par1)))))
            (.seq
            (.prefix .wel (.atom .par3))
            (.seq
            (.seq
            (.prefix .par2 (.atom .wel))
            (.prefix .cons (.seq (.prefix .cons (.prefix .par1 (.atom .par2))) (.atom .par3))))
            (.seq
            (.prefix .cons (.atom .wal))
            (.seq
            (.seq (.prefix .par1 (.atom .par2)) (.atom .wal))
            (.seq
            (.seq (.prefix .par1 (.atom .par3)) (.atom .wal))
            (.seq
            (.prefix .cons (.prefix .cons (.prefix .par1 (.prefix .par1 (.atom .par2)))))
            (.prefix .weq
            (.seq
            (.prefix .wex (.atom .par2))
            (.seq
            (.seq (.prefix .par1 (.prefix .par1 (.atom .par2))) (.atom .wel))
            (.seq
            (.seq (.prefix .par3 (.atom .par2)) (.atom .par3))
            (.prefix .par3
            (.seq
            (.prefix .par2 (.seq (.prefix .wel (.atom .par3)) (.atom .par1)))
            (.seq
            (.prefix .wel (.prefix .cons (.atom .wal)))
            (.seq
            (.prefix .par2 (.prefix .par3 (.atom .wel)))
            (.seq
            (.seq
            (.prefix .cons (.atom .wal))
            (.prefix .par3
            (.seq (.prefix .par2 (.atom .wel)) (.seq (.prefix .wa (.atom .wex)) (.atom .par3)))))
            (.seq
            (.prefix .par3 (.atom .par1))
            (.seq
            (.prefix .wel (.atom .par3))
            (.prefix .par2
            (.seq
            (.prefix .wel (.prefix .cons (.atom .wal)))
            (.prefix .wa
            (.seq
            (.seq
            (.prefix .cons (.atom .wal))
            (.prefix .par3
            (.seq (.prefix .par2 (.atom .wel)) (.seq (.prefix .wa (.atom .wex)) (.atom .par3)))))
            (.seq
            (.seq (.prefix .par1 (.prefix .par1 (.atom .par2))) (.atom .wel))
            (.seq
            (.prefix .par2 (.seq (.prefix .par3 (.atom .par2)) (.atom .par3)))
            (.seq
            (.prefix .par2 (.prefix .par3 (.atom .wel)))
            (.prefix .wa
            (.seq
            (.prefix .wex (.prefix .cons (.atom .wal)))
            (.seq
            (.prefix .cons (.atom .wal))
            (.prefix .par2
            (.seq
            (.prefix .par2 (.prefix .par3 (.atom .wel)))
            (.seq
            (.prefix .par1 (.atom .par3))
            (.seq
            (.prefix .wex (.prefix .cons (.atom .wal)))
            (.seq
            (.prefix .wa (.atom .wex))
            (.prefix .wa
            (.prefix .par1
            (.seq
            (.prefix .par2 (.seq (.prefix .wel (.atom .par3)) (.atom .par1)))
            (.seq
            (.prefix .par2 (.atom .wel))
            (.seq
            (.prefix .wal
            (.seq
            (.prefix .cons (.prefix .par1 (.atom .par2)))
            (.prefix .weq (.prefix .par3 (.atom .par1)))))
            (.seq
            (.prefix .par2 (.atom .weq))
            (.prefix .wal (.prefix .cons (.prefix .wa (.prefix .wa .gate))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem axExpr_checked : axExprCheck dag254 71 1 axExpr = true := by decide +kernel

def f1 (st : AS) : AS := axExprEval axExpr st

theorem l1 (st : AS) (hc : Clean st) : Rn (.node 1) st (f1 st) :=
  axExprRun (fun _ {_ _} h => h) loop208
    (fun st hc => by
      have := seqAS (n := 71) rfl (loop192 st) (seqAS (n := 72) rfl (ifeq_clear _)
        (seqAS (n := 73) rfl (loop211 _) (seqAS (n := 74) rfl (loop197 _) (ifeq_clear _))))
      apply rn_eq this
      obtain ⟨h1, h2⟩ := hc
      cases st
      simp only at h1 h2
      subst h1; subst h2
      simp only [gateF, Nat.zero_add]
      split <;> split <;> simp_all <;> omega) axExpr axExpr_checked st hc

theorem c1 (st : AS) (hc : Clean st) : Clean (f1 st) := axExprClean axExpr st hc

set_option maxHeartbeats 1000000 in
/-- The native AX effect is the enumerator AX step. -/
theorem ax_eval (np t S c a h pl : Nat) :
    f1 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, Enum254.gate a (h + (Cantor.ofNat pl).1) c,
        Enum254.axStack a h (h + (Cantor.ofNat pl).1) c (Cantor.ofNat (Cantor.ofNat pl).2).1 t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := by
  simp only [f1, axExpr, axExprEval, AXAtom.effect, pushA, popA, gateF, ofNat_P,
    Enum254.gate, Enum254.axStack, bundle, bundleC, bundleG, rho1, rho2, rho3, rho4, rho5,
    rho6, rho7, rho8, Nat.zero_add]

end SetTheory.BusyBeaver.ZFC.L2
