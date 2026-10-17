import BusyBeaver.ZFC.Kalmar
import BusyBeaver.ZFC.TarskiCalculus

/-!
Proposed Lean adapter for the explicit public CD254 mathematical proof DAG.
Source: https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/logic/CD254.v
The JSON certificate is replayed independently by verify_basis.py.
STATUS: generated source; not compiled in the delivery environment.
No machine compiler or internal-ZFC endpoint follows from this adapter alone.
-/

namespace SetTheory.BusyBeaver.ZFC.Tarski
open NF
namespace LukasiewiczCertificate
variable {Ax : NF → Prop}

theorem cd_0 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 v1) v2) (imp (imp v2 v0) (imp v3 v0))) :=
  .rho8 v0 v1 v2 v3

theorem cd_1 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp (imp (imp v0 v1) (imp v2 v1)) (imp v1 v3)) (imp v4 (imp v1 v3))) :=
  .mp (cd_0 (imp v1 v3) v0 (imp (imp v0 v1) (imp v2 v1)) v4) (cd_0 v1 v3 v0 v2)

theorem cd_2 (v0 v1 v2 : NF) : Thm Ax (imp v0 (imp (imp v1 v2) (imp v2 (imp v1 v2)))) :=
  .mp (cd_1 (imp NF.bot v2) (imp v1 v2) v2 (imp v2 (imp v1 v2)) v0) (cd_1 NF.bot v2 v1 (imp v1 v2) (imp v1 v2))

theorem cd_3 (v0 v1 : NF) : Thm Ax (imp (imp v0 v1) (imp v1 (imp v0 v1))) :=
  .mp (cd_2 (imp (imp (imp NF.bot NF.bot) NF.bot) (imp (imp NF.bot NF.bot) (imp NF.bot NF.bot))) v0 v1) (cd_0 NF.bot NF.bot NF.bot NF.bot)

theorem cd_4 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp v0 (imp v1 v0)) v1) (imp v2 v1)) :=
  .mp (cd_0 v1 v0 (imp v0 (imp v1 v0)) v2) (cd_3 v1 v0)

theorem cd_5 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 v1) (imp v2 (imp v1 v2))) (imp v3 (imp v2 (imp v1 v2)))) :=
  .mp (cd_0 (imp v2 (imp v1 v2)) v1 (imp v0 v1) v3) (cd_4 v2 v1 v0)

theorem cd_6 (v0 v1 : NF) : Thm Ax (imp v0 (imp v1 (imp v1 v1))) :=
  .mp (cd_5 v1 v1 v1 v0) (cd_3 v1 v1)

theorem cd_7 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp v0 (imp v0 v0)) v1) (imp v2 v1)) :=
  .mp (cd_0 v1 NF.bot (imp v0 (imp v0 v0)) v2) (cd_6 (imp v1 NF.bot) v0)

theorem cd_8 (v0 v1 v2 : NF) : Thm Ax (imp v0 (imp (imp v1 v1) (imp v2 (imp v1 v1)))) :=
  .mp (cd_1 v1 (imp v1 v1) v2 (imp v2 (imp v1 v1)) v0) (cd_7 v1 (imp v2 (imp v1 v1)) (imp v1 v1))

theorem cd_9 (v0 v1 : NF) : Thm Ax (imp (imp v0 v0) (imp v1 (imp v0 v0))) :=
  .mp (cd_8 (imp (imp (imp NF.bot NF.bot) NF.bot) (imp (imp NF.bot NF.bot) (imp NF.bot NF.bot))) v0 v1) (cd_0 NF.bot NF.bot NF.bot NF.bot)

theorem cd_10 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp v0 (imp v1 v1)) v1) (imp v2 v1)) :=
  .mp (cd_0 v1 v1 (imp v0 (imp v1 v1)) v2) (cd_9 v1 v0)

theorem cd_11 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 v1) (imp v2 (imp v1 v1))) (imp v3 (imp v2 (imp v1 v1)))) :=
  .mp (cd_0 (imp v2 (imp v1 v1)) v1 (imp v0 v1) v3) (cd_10 v2 v1 v0)

theorem cd_12 (v0 v1 v2 : NF) : Thm Ax (imp v0 (imp v1 (imp v2 v2))) :=
  .mp (cd_11 v2 v2 v1 v0) (cd_9 v2 v1)

theorem cd_13 (v0 v1 : NF) : Thm Ax (imp v0 (imp v1 v1)) :=
  .mp (cd_12 (imp (imp (imp NF.bot NF.bot) NF.bot) (imp (imp NF.bot NF.bot) (imp NF.bot NF.bot))) v0 v1) (cd_0 NF.bot NF.bot NF.bot NF.bot)

theorem cd_14 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp v0 v0) v1) (imp v2 v1)) :=
  .mp (cd_0 v1 NF.bot (imp v0 v0) v2) (cd_13 (imp v1 NF.bot) v0)

theorem cd_15 (v0 v1 v2 : NF) : Thm Ax (imp v0 (imp v1 (imp v2 v1))) :=
  .mp (cd_1 v1 v1 v2 (imp v2 v1) v0) (cd_14 v1 (imp v2 v1) v1)

theorem cd_16 (v0 v1 : NF) : Thm Ax (imp v0 (imp v1 v0)) :=
  .mp (cd_15 (imp (imp (imp NF.bot NF.bot) NF.bot) (imp (imp NF.bot NF.bot) (imp NF.bot NF.bot))) v0 v1) (cd_0 NF.bot NF.bot NF.bot NF.bot)

theorem cd_17 (v0 : NF) : Thm Ax (imp v0 v0) :=
  .mp (cd_13 (imp (imp (imp NF.bot NF.bot) NF.bot) (imp (imp NF.bot NF.bot) (imp NF.bot NF.bot))) v0) (cd_0 NF.bot NF.bot NF.bot NF.bot)

theorem cd_18 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp v0 v1) v0) (imp v2 v0)) :=
  .mp (cd_0 v0 v1 (imp v0 v1) v2) (cd_17 (imp v0 v1))

theorem cd_19 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 v1) (imp v1 v2)) (imp v3 (imp v1 v2))) :=
  .mp (cd_0 (imp v1 v2) v1 (imp v0 v1) v3) (cd_18 v1 v2 v0)

theorem cd_20 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp (imp v0 (imp v1 v2)) (imp v3 v1)) (imp v4 (imp v3 v1))) :=
  .mp (cd_0 (imp v3 v1) (imp v1 v2) (imp v0 (imp v1 v2)) v4) (cd_19 v3 v1 v2 v0)

theorem cd_21 (v0 v1 v2 v3 : NF) : Thm Ax (imp v0 (imp (imp (imp (imp v1 v2) v3) v2) (imp v1 v2))) :=
  .mp (cd_20 (imp v2 NF.bot) (imp v1 v2) v3 (imp (imp (imp v1 v2) v3) v2) v0) (cd_0 v2 NF.bot (imp (imp v1 v2) v3) v1)

theorem cd_22 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp (imp v0 v1) v2) v1) (imp v0 v1)) :=
  .mp (cd_21 (imp (imp (imp NF.bot NF.bot) NF.bot) (imp (imp NF.bot NF.bot) (imp NF.bot NF.bot))) v0 v1 v2) (cd_0 NF.bot NF.bot NF.bot NF.bot)

theorem cd_23 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 v1) (imp (imp v0 v1) v2)) (imp v3 (imp (imp v0 v1) v2))) :=
  .mp (cd_0 (imp (imp v0 v1) v2) v1 (imp v0 v1) v3) (cd_22 v0 v1 v2)

theorem cd_24 (v0 v1 v2 : NF) : Thm Ax (imp v0 (imp (imp (imp v1 v2) v1) v1)) :=
  .mp (cd_23 (imp v1 v2) v1 v1 v0) (cd_18 v1 v2 (imp (imp v1 v2) v1))

theorem cd_25 (v0 v1 : NF) : Thm Ax (imp (imp (imp v0 v1) v0) v0) :=
  .mp (cd_24 (imp (imp (imp NF.bot NF.bot) NF.bot) (imp (imp NF.bot NF.bot) (imp NF.bot NF.bot))) v0 v1) (cd_0 NF.bot NF.bot NF.bot NF.bot)

theorem cd_26 (v0 v1 v2 : NF) : Thm Ax (imp (imp v0 (imp v0 v1)) (imp v2 (imp v0 v1))) :=
  .mp (cd_0 (imp v0 v1) v0 v0 v2) (cd_25 v0 v1)

theorem cd_27 (v0 v1 v2 : NF) : Thm Ax (imp v0 (imp (imp v1 (imp v1 v2)) (imp v1 v2))) :=
  .mp (cd_23 v1 (imp v1 v2) (imp v1 v2) v0) (cd_26 v1 v2 (imp v1 (imp v1 v2)))

theorem cd_28 (v0 v1 : NF) : Thm Ax (imp (imp v0 (imp v0 v1)) (imp v0 v1)) :=
  .mp (cd_27 (imp (imp (imp NF.bot NF.bot) NF.bot) (imp (imp NF.bot NF.bot) (imp NF.bot NF.bot))) v0 v1) (cd_0 NF.bot NF.bot NF.bot NF.bot)

theorem cd_29 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp v0 v1) (imp v1 v2)) (imp v1 v2)) :=
  .mp (cd_28 (imp (imp v0 v1) (imp v1 v2)) (imp v1 v2)) (cd_19 v0 v1 v2 (imp (imp v0 v1) (imp v1 v2)))

theorem cd_30 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 v1) (imp v2 v0)) (imp v3 (imp v2 v0))) :=
  .mp (cd_0 (imp v2 v0) (imp v0 v1) (imp v0 v1) v3) (cd_29 v2 v0 v1)

theorem cd_31 (v0 v1 v2 : NF) : Thm Ax (imp v0 (imp v1 (imp v2 v0))) :=
  .mp (cd_22 v0 (imp v1 (imp v2 v0)) (imp v2 v0)) (cd_30 v0 (imp v1 (imp v2 v0)) v2 v1)

theorem cd_32 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp (imp v0 (imp v1 (imp v2 v3))) v2) (imp v4 v2)) :=
  .mp (cd_0 v2 v3 (imp v0 (imp v1 (imp v2 v3))) v4) (cd_31 (imp v2 v3) v0 v1)

theorem cd_33 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 (imp v1 (imp v2 v3))) v2) v2) :=
  .mp (cd_28 (imp (imp v0 (imp v1 (imp v2 v3))) v2) v2) (cd_32 v0 v1 v2 v3 (imp (imp v0 (imp v1 (imp v2 v3))) v2))

theorem cd_34 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp v0 (imp v1 (imp v2 (imp v0 v3)))) (imp v4 (imp v1 (imp v2 (imp v0 v3))))) :=
  .mp (cd_0 (imp v1 (imp v2 (imp v0 v3))) v0 v0 v4) (cd_33 v1 v2 v0 v3)

theorem cd_35 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp v0 (imp v1 (imp v2 (imp v0 v3)))) (imp v1 (imp v2 (imp v0 v3)))) :=
  .mp (cd_28 (imp v0 (imp v1 (imp v2 (imp v0 v3)))) (imp v1 (imp v2 (imp v0 v3)))) (cd_34 v0 v1 v2 v3 (imp v0 (imp v1 (imp v2 (imp v0 v3)))))

theorem cd_36 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp (imp v0 v1) (imp v1 (imp v0 v1))) v2) (imp v3 v2)) :=
  .mp (cd_0 v2 NF.bot (imp (imp v0 v1) (imp v1 (imp v0 v1))) v3) (cd_2 (imp v2 NF.bot) v0 v1)

theorem cd_37 (v0 v1 v2 v3 : NF) : Thm Ax (imp v0 (imp (imp (imp v1 (imp v2 v1)) v2) (imp v3 v2))) :=
  .mp (cd_36 v2 v1 (imp (imp (imp v1 (imp v2 v1)) v2) (imp v3 v2)) v0) (cd_0 v2 v1 (imp v1 (imp v2 v1)) v3)

theorem cd_38 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp (imp (imp (imp v0 (imp v1 v0)) v1) (imp v2 v1)) v3) (imp v4 v3)) :=
  .mp (cd_0 v3 NF.bot (imp (imp (imp v0 (imp v1 v0)) v1) (imp v2 v1)) v4) (cd_37 (imp v3 NF.bot) v0 v1 v2)

theorem cd_39 (v0 v1 v2 v3 : NF) : Thm Ax (imp v0 (imp (imp v1 v2) (imp v3 (imp v1 v2)))) :=
  .mp (cd_1 (imp (imp NF.bot (imp v2 NF.bot)) v2) (imp v1 v2) v3 (imp v3 (imp v1 v2)) v0) (cd_38 NF.bot v2 v1 (imp v3 (imp v1 v2)) (imp v1 v2))

theorem cd_40 (v0 v1 v2 : NF) : Thm Ax (imp (imp v0 v1) (imp v2 (imp v0 v1))) :=
  .mp (cd_39 (imp (imp (imp NF.bot NF.bot) NF.bot) (imp (imp NF.bot NF.bot) (imp NF.bot NF.bot))) v0 v1 v2) (cd_0 NF.bot NF.bot NF.bot NF.bot)

theorem cd_41 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 (imp v1 v2)) v1) (imp v3 v1)) :=
  .mp (cd_0 v1 v2 (imp v0 (imp v1 v2)) v3) (cd_40 v1 v2 v0)

theorem cd_42 (v0 v1 v2 v3 : NF) : Thm Ax (imp v0 (imp (imp (imp v1 (imp v2 v3)) v2) v2)) :=
  .mp (cd_23 (imp v1 (imp v2 v3)) v2 v2 v0) (cd_41 v1 v2 v3 (imp (imp v1 (imp v2 v3)) v2))

theorem cd_43 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp v0 (imp v1 v2)) v1) v1) :=
  .mp (cd_42 (imp (imp (imp NF.bot NF.bot) NF.bot) (imp (imp NF.bot NF.bot) (imp NF.bot NF.bot))) v0 v1 v2) (cd_0 NF.bot NF.bot NF.bot NF.bot)

theorem cd_44 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp v0 (imp v1 (imp v0 v2))) (imp v3 (imp v1 (imp v0 v2)))) :=
  .mp (cd_0 (imp v1 (imp v0 v2)) v0 v0 v3) (cd_43 v1 v0 v2)

theorem cd_45 (v0 v1 v2 : NF) : Thm Ax (imp (imp v0 (imp v1 (imp v0 v2))) (imp v1 (imp v0 v2))) :=
  .mp (cd_28 (imp v0 (imp v1 (imp v0 v2))) (imp v1 (imp v0 v2))) (cd_44 v0 v1 v2 (imp v0 (imp v1 (imp v0 v2))))

theorem cd_46 (v0 v1 v2 v3 : NF) : Thm Ax (imp v0 (imp (imp v1 v2) (imp (imp (imp v2 v3) v1) v2))) :=
  .mp (cd_44 (imp (imp v2 v3) v1) (imp v1 v2) v2 v0) (cd_0 v2 v3 v1 (imp (imp v2 v3) v1))

theorem cd_47 (v0 v1 v2 : NF) : Thm Ax (imp (imp v0 v1) (imp (imp (imp v1 v2) v0) v1)) :=
  .mp (cd_46 (imp (imp (imp NF.bot NF.bot) NF.bot) (imp (imp NF.bot NF.bot) (imp NF.bot NF.bot))) v0 v1 v2) (cd_0 NF.bot NF.bot NF.bot NF.bot)

theorem cd_48 (v0 v1 v2 v3 v4 v5 : NF) : Thm Ax (imp (imp (imp v0 (imp v1 v2)) (imp v3 (imp v2 v4))) (imp v5 (imp v3 (imp v2 v4)))) :=
  .mp (cd_0 (imp v3 (imp v2 v4)) (imp v1 v2) (imp v0 (imp v1 v2)) v5) (cd_20 v3 v2 v4 v1 v0)

theorem cd_49 (v0 v1 v2 v3 : NF) : Thm Ax (imp v0 (imp (imp (imp v1 v2) v3) (imp v2 v3))) :=
  .mp (cd_48 (imp v3 NF.bot) v1 v2 (imp (imp v1 v2) v3) v3 v0) (cd_0 v3 NF.bot (imp v1 v2) v2)

theorem cd_50 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp v0 v1) v2) (imp v1 v2)) :=
  .mp (cd_49 (imp (imp (imp NF.bot NF.bot) NF.bot) (imp (imp NF.bot NF.bot) (imp NF.bot NF.bot))) v0 v1 v2) (cd_0 NF.bot NF.bot NF.bot NF.bot)

theorem cd_51 (v0 v1 v2 : NF) : Thm Ax (imp v0 (imp (imp v0 v1) (imp v2 v1))) :=
  .mp (cd_50 (imp v1 NF.bot) v0 (imp (imp v0 v1) (imp v2 v1))) (cd_0 v1 NF.bot v0 v2)

theorem cd_52 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp (imp (imp v0 v1) (imp v2 v1)) v3) v0) (imp (imp v0 v1) (imp v2 v1))) :=
  .mp (cd_47 v0 (imp (imp v0 v1) (imp v2 v1)) v3) (cd_51 v0 v1 v2)

theorem cd_53 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp (imp v0 v1) v2) (imp (imp v1 v3) v1)) (imp v0 v1)) :=
  .mp (cd_47 (imp (imp v1 v3) v1) (imp v0 v1) v2) (cd_18 v1 v3 v0)

theorem cd_54 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp (imp (imp v0 v1) v2) (imp (imp v3 (imp v1 v4)) v1)) (imp v0 v1)) :=
  .mp (cd_47 (imp (imp v3 (imp v1 v4)) v1) (imp v0 v1) v2) (cd_41 v3 v1 v4 v0)

theorem cd_55 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp (imp (imp (imp v0 v1) v2) (imp v3 v2)) v0) (imp v4 v0)) :=
  .mp (cd_0 v0 v1 (imp (imp (imp v0 v1) v2) (imp v3 v2)) v4) (cd_51 (imp v0 v1) v2 v3)

theorem cd_56 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp (imp (imp v0 v1) v2) (imp v3 v2)) v0) v0) :=
  .mp (cd_28 (imp (imp (imp (imp v0 v1) v2) (imp v3 v2)) v0) v0) (cd_55 v0 v1 v2 v3 (imp (imp (imp (imp v0 v1) v2) (imp v3 v2)) v0))

theorem cd_57 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp (imp (imp (imp v0 (imp (imp v1 v2) v3)) (imp v1 v2)) v4) v2) (imp v1 v2)) :=
  .mp (cd_54 (imp (imp (imp (imp v0 (imp (imp v1 v2) v3)) (imp v1 v2)) v4) v2) (imp v1 v2) (imp (imp v0 (imp (imp v1 v2) v3)) (imp v1 v2)) v0 v3) (cd_56 (imp (imp v0 (imp (imp v1 v2) v3)) (imp v1 v2)) v4 v2 v1)

theorem cd_58 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 (imp (imp (imp v1 v2) v1) v3)) (imp (imp v1 v2) v1)) v1) :=
  .mp (cd_53 (imp (imp v0 (imp (imp (imp v1 v2) v1) v3)) (imp (imp v1 v2) v1)) v1 v1 v2) (cd_57 v0 (imp v1 v2) v1 v3 v1)

theorem cd_59 (v0 v1 v2 : NF) : Thm Ax (imp (imp v0 v1) (imp (imp (imp v0 v2) v0) v1)) :=
  .mp (cd_52 v0 v1 (imp (imp v0 v2) v0) (imp (imp v0 v2) v0)) (cd_58 (imp v0 v1) v0 v2 v1)

theorem cd_60 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp (imp v0 (imp v1 v2)) v3) (imp v1 (imp v1 v2))) (imp v0 (imp v1 v2))) :=
  .mp (cd_47 (imp v1 (imp v1 v2)) (imp v0 (imp v1 v2)) v3) (cd_26 v1 v2 v0)

theorem cd_61 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 v1) v0) (imp (imp v0 v2) (imp v3 v2))) :=
  .mp (cd_59 v0 (imp (imp v0 v2) (imp v3 v2)) v1) (cd_51 v0 v2 v3)

theorem cd_62 (v0 v1 : NF) : Thm Ax (imp v0 (imp (imp v0 v1) v1)) :=
  .mp (cd_60 v0 (imp v0 v1) v1 v0) (cd_61 v0 (imp (imp v0 v1) v1) v1 (imp v0 v1))

theorem cd_63 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp v0 v1) v0) (imp (imp v0 v2) v2)) :=
  .mp (cd_59 v0 (imp (imp v0 v2) v2) v1) (cd_62 v0 v2)

theorem cd_64 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp (imp v0 v1) v1) (imp v0 v2)) (imp v3 (imp v0 v2))) :=
  .mp (cd_0 (imp v0 v2) v0 (imp (imp v0 v1) v1) v3) (cd_63 v0 v2 v1)

theorem cd_65 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp (imp v0 v1) v1) (imp v0 v2)) (imp v0 v2)) :=
  .mp (cd_28 (imp (imp (imp v0 v1) v1) (imp v0 v2)) (imp v0 v2)) (cd_64 v0 v1 v2 (imp (imp (imp v0 v1) v1) (imp v0 v2)))

theorem cd_66 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp (imp v0 (imp v1 v2)) v3) v2) (imp v0 (imp v1 v2))) :=
  .mp (cd_47 v2 (imp v0 (imp v1 v2)) v3) (cd_31 v2 v0 v1)

theorem cd_67 (v0 v1 v2 v3 : NF) : Thm Ax (imp v0 (imp v1 (imp (imp v0 v2) (imp v3 v2)))) :=
  .mp (cd_66 v0 v1 (imp (imp v0 v2) (imp v3 v2)) v0) (cd_61 v0 (imp v1 (imp (imp v0 v2) (imp v3 v2))) v2 v3)

theorem cd_68 (v0 v1 v2 v3 : NF) : Thm Ax (imp v0 (imp (imp (imp (imp v0 v1) v1) v2) (imp v3 v2))) :=
  .mp (cd_65 v0 v1 (imp (imp (imp (imp v0 v1) v1) v2) (imp v3 v2))) (cd_67 (imp (imp v0 v1) v1) v0 v2 v3)

theorem cd_69 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp (imp v0 v1) v1) v2) (imp v0 v2)) :=
  .mp (cd_45 v0 (imp (imp (imp v0 v1) v1) v2) v2) (cd_68 v0 v1 v2 v0)

theorem cd_70 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp (imp v0 v1) (imp v2 (imp v1 v3))) (imp v4 (imp v2 (imp v1 v3)))) :=
  .mp (cd_0 (imp v2 (imp v1 v3)) v1 (imp v0 v1) v4) (cd_41 v2 v1 v3 v0)

theorem cd_71 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 v1) (imp v2 (imp v1 v3))) (imp v2 (imp v1 v3))) :=
  .mp (cd_28 (imp (imp v0 v1) (imp v2 (imp v1 v3))) (imp v2 (imp v1 v3))) (cd_70 v0 v1 v2 v3 (imp (imp v0 v1) (imp v2 (imp v1 v3))))

theorem cd_72 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp v0 (imp v1 (imp (imp (imp v2 v0) v3) (imp v4 v3)))) :=
  .mp (cd_50 v2 v0 (imp v1 (imp (imp (imp v2 v0) v3) (imp v4 v3)))) (cd_67 (imp v2 v0) v1 v3 v4)

theorem cd_73 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp v0 (imp (imp (imp v1 (imp (imp v0 v2) v2)) v3) (imp v4 v3))) :=
  .mp (cd_65 v0 v2 (imp (imp (imp v1 (imp (imp v0 v2) v2)) v3) (imp v4 v3))) (cd_72 (imp (imp v0 v2) v2) v0 v1 v3 v4)

theorem cd_74 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp (imp v0 (imp (imp (imp v1 v2) v3) v3)) v4) (imp v2 v4)) :=
  .mp (cd_71 v1 v2 (imp (imp v0 (imp (imp (imp v1 v2) v3) v3)) v4) v4) (cd_73 (imp v1 v2) v0 v3 v4 v2)

theorem cd_75 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 v1) v2) (imp (imp (imp v3 v0) v2) v2)) :=
  .mp (cd_52 (imp v0 v1) v2 (imp (imp v3 v0) v2) v1) (cd_74 (imp (imp v0 v1) v2) v3 v0 v2 v1)

theorem cd_76 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp (imp (imp v0 v1) v1) v2) v0) (imp (imp v0 v1) v1)) :=
  .mp (cd_47 v0 (imp (imp v0 v1) v1) v2) (cd_62 v0 v1)

theorem cd_77 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp v0 v1) (imp v2 v0)) (imp v2 v0)) :=
  .mp (cd_28 (imp (imp v0 v1) (imp v2 v0)) (imp v2 v0)) (cd_30 v0 v1 v2 (imp (imp v0 v1) (imp v2 v0)))

theorem cd_78 (v0 v1 v2 : NF) : Thm Ax (imp v0 (imp v1 (imp (imp v0 v2) v2))) :=
  .mp (cd_66 v0 v1 (imp (imp v0 v2) v2) v0) (cd_63 v0 (imp v1 (imp (imp v0 v2) v2)) v2)

theorem cd_79 (v0 v1 v2 v3 : NF) : Thm Ax (imp v0 (imp v1 (imp (imp (imp v2 v0) v3) v3))) :=
  .mp (cd_50 v2 v0 (imp v1 (imp (imp (imp v2 v0) v3) v3))) (cd_78 (imp v2 v0) v1 v3)

theorem cd_80 (v0 v1 v2 v3 : NF) : Thm Ax (imp v0 (imp (imp (imp v1 (imp (imp v0 v2) v2)) v3) v3)) :=
  .mp (cd_65 v0 v2 (imp (imp (imp v1 (imp (imp v0 v2) v2)) v3) v3)) (cd_79 (imp (imp v0 v2) v2) v0 v1 v3)

theorem cd_81 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 (imp (imp (imp v1 v2) v3) v3)) v1) v1) :=
  .mp (cd_77 v1 v2 (imp (imp v0 (imp (imp (imp v1 v2) v3) v3)) v1)) (cd_80 (imp v1 v2) v0 v3 v1)

theorem cd_82 (v0 v1 v2 : NF) : Thm Ax (imp (imp v0 (imp (imp (imp v0 v1) v2) v2)) (imp (imp (imp v0 v1) v2) v2)) :=
  .mp (cd_76 v0 (imp (imp (imp v0 v1) v2) v2) v0) (cd_81 (imp v0 (imp (imp (imp v0 v1) v2) v2)) v0 v1 v2)

theorem cd_83 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 (imp v1 v2)) (imp v3 v1)) (imp v3 v1)) :=
  .mp (cd_28 (imp (imp v0 (imp v1 v2)) (imp v3 v1)) (imp v3 v1)) (cd_20 v0 v1 v2 v3 (imp (imp v0 (imp v1 v2)) (imp v3 v1)))

theorem cd_84 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp (imp v0 (imp (imp (imp v1 (imp v2 v3)) v4) v4)) v2) v2) :=
  .mp (cd_83 v1 v2 v3 (imp (imp v0 (imp (imp (imp v1 (imp v2 v3)) v4) v4)) v2)) (cd_80 (imp v1 (imp v2 v3)) v0 v4 v2)

theorem cd_85 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp v0 v1) (imp (imp (imp v2 (imp v0 v3)) v1) v1)) :=
  .mp (cd_52 v0 v1 (imp (imp v2 (imp v0 v3)) v1) v0) (cd_84 (imp v0 v1) v2 v0 v3 v1)

theorem cd_86 (v0 v1 v2 : NF) : Thm Ax (imp (imp (imp (imp v0 v1) (imp v0 v2)) v1) v1) :=
  .mp (cd_82 (imp v0 v1) (imp v0 v2) v1) (cd_85 v0 v1 (imp v0 v1) v2)

theorem cd_87 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp v0 (imp (imp v1 v2) (imp v1 v3))) v2) v2) :=
  .mp (cd_75 (imp (imp v1 v2) (imp v1 v3)) v2 v2 v0) (cd_86 v1 v2 v3)

theorem cd_88 (v0 v1 v2 : NF) : Thm Ax (imp (imp v0 (imp v1 v2)) (imp (imp v1 v0) (imp v1 v2))) :=
  .mp (cd_52 v0 (imp v1 v2) (imp v1 v0) v0) (cd_87 (imp v0 (imp v1 v2)) v1 v0 v2)

theorem cd_89 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp v0 v1) (imp v0 (imp (imp v1 v2) (imp v3 v2)))) :=
  .mp (cd_88 v1 v0 (imp (imp v1 v2) (imp v3 v2))) (cd_67 v1 v0 v2 v3)

theorem cd_90 (v0 v1 v2 v3 : NF) : Thm Ax (imp v0 (imp (imp v0 v1) (imp (imp v1 v2) (imp v3 v2)))) :=
  .mp (cd_69 v0 v1 (imp (imp v0 v1) (imp (imp v1 v2) (imp v3 v2)))) (cd_89 (imp v0 v1) v1 v2 v3)

theorem cd_91 (v0 v1 v2 : NF) : Thm Ax (imp (imp v0 v1) (imp (imp v1 v2) (imp v0 v2))) :=
  .mp (cd_35 v0 (imp v0 v1) (imp v1 v2) v2) (cd_90 v0 v1 v2 v0)

theorem cd_92 (v0 v1 v2 : NF) : Thm Ax (imp v0 (imp (imp (imp v1 v0) v2) v2)) :=
  .mp (cd_50 v1 v0 (imp (imp (imp v1 v0) v2) v2)) (cd_62 (imp v1 v0) v2)

theorem cd_93 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp (imp (imp (imp v0 (imp v1 v2)) v3) v3) v1) (imp v4 v1)) :=
  .mp (cd_0 v1 v2 (imp (imp (imp v0 (imp v1 v2)) v3) v3) v4) (cd_92 (imp v1 v2) v0 v3)

theorem cd_94 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp (imp (imp v0 (imp v1 v2)) v3) v3) v1) v1) :=
  .mp (cd_28 (imp (imp (imp (imp v0 (imp v1 v2)) v3) v3) v1) v1) (cd_93 v0 v1 v2 v3 (imp (imp (imp (imp v0 (imp v1 v2)) v3) v3) v1))

theorem cd_95 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp (imp v0 (imp (imp (imp v1 (imp v2 v3)) v2) v4)) v2) v2) :=
  .mp (cd_54 (imp (imp v0 (imp (imp (imp v1 (imp v2 v3)) v2) v4)) v2) v2 (imp (imp v1 (imp v2 v3)) v2) v1 v3) (cd_94 v0 (imp (imp v1 (imp v2 v3)) v2) v4 v2)

theorem cd_96 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp v0 v1) (imp (imp (imp v2 (imp v0 v3)) v0) v1)) :=
  .mp (cd_52 v0 v1 (imp (imp v2 (imp v0 v3)) v0) v0) (cd_95 (imp v0 v1) v2 v0 v3 v1)

theorem cd_97 (v0 v1 v2 v3 v4 : NF) : Thm Ax (imp (imp (imp v0 (imp v1 v2)) v1) (imp (imp v1 v3) (imp v4 v3))) :=
  .mp (cd_96 v1 (imp (imp v1 v3) (imp v4 v3)) v0 v2) (cd_51 v1 v3 v4)

theorem cd_98 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp (imp v0 v1) (imp v2 v1)) v3) (imp v0 v3)) :=
  .mp (cd_52 (imp (imp v0 v1) (imp v2 v1)) v3 v0 v0) (cd_97 (imp (imp (imp v0 v1) (imp v2 v1)) v3) v0 v3 v1 v2)

theorem cd_99 (v0 v1 v2 : NF) : Thm Ax (imp (imp v0 v1) (imp v0 (imp v2 v1))) :=
  .mp (cd_98 (imp v0 v1) v1 v2 (imp v0 (imp v2 v1))) (cd_69 v0 v1 (imp v2 v1))

theorem cd_100 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp v0 v1) (imp v2 (imp v0 (imp v3 v1)))) :=
  .mp (cd_99 (imp v0 v1) (imp v0 (imp v3 v1)) v2) (cd_99 v0 v1 v3)

theorem cd_101 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp v0 (imp v1 v2)) (imp v0 (imp v1 (imp v3 v2)))) :=
  .mp (cd_88 (imp v1 v2) v0 (imp v1 (imp v3 v2))) (cd_100 v1 v2 v0 v3)

theorem cd_102 (v0 v1 v2 v3 : NF) : Thm Ax (imp v0 (imp (imp v0 (imp v1 v2)) (imp v1 (imp v3 v2)))) :=
  .mp (cd_69 v0 (imp v1 v2) (imp (imp v0 (imp v1 v2)) (imp v1 (imp v3 v2)))) (cd_101 (imp v0 (imp v1 v2)) v1 v2 v3)

theorem cd_103 (v0 v1 v2 : NF) : Thm Ax (imp (imp v0 (imp v1 v2)) (imp v1 (imp v0 v2))) :=
  .mp (cd_35 v0 (imp v0 (imp v1 v2)) v1 v2) (cd_102 v0 v1 v2 v0)

theorem cd_104 (v0 v1 v2 v3 : NF) : Thm Ax (imp (imp (imp (imp v0 v1) (imp v2 v1)) v3) (imp (imp v2 v0) v3)) :=
  .mp (cd_91 (imp v2 v0) (imp (imp v0 v1) (imp v2 v1)) v3) (cd_91 v2 v0 v1)

theorem cd_105 (v0 v1 v2 : NF) : Thm Ax (imp (imp v0 v1) (imp (imp v0 (imp v1 v2)) (imp v0 v2))) :=
  .mp (cd_104 v1 v2 v0 (imp (imp v0 (imp v1 v2)) (imp v0 v2))) (cd_88 (imp v1 v2) v0 v2)

theorem cd_106 (v0 v1 v2 : NF) : Thm Ax (imp (imp v0 (imp v1 v2)) (imp (imp v0 v1) (imp v0 v2))) :=
  .mp (cd_103 (imp v0 v1) (imp v0 (imp v1 v2)) (imp v0 v2)) (cd_105 v0 v1 v2)

end LukasiewiczCertificate

open LukasiewiczCertificate

/-- Explosion uses rho6 in addition to the implication basis. -/
theorem certificate_exfalso {Ax : NF → Prop} (a : NF) : Thm Ax (imp NF.bot a) := by
  let e := ex 0 (all 0 a)
  have hk : Thm Ax (imp NF.bot e) := cd_16 NF.bot (all 0 (neg (all 0 a)))
  have hb : Thm Ax (imp (imp NF.bot e) (imp (imp e a) (imp NF.bot a))) :=
    cd_91 NF.bot e a
  exact .mp (.mp hb hk) (.rho6 0 a)

/-- Discharges both classical-basis parameters of Tarski.completeness. -/
theorem certificate_classical (Ax : NF → Prop) :
    Kalmar.Classical NF.imp NF.bot (Thm Ax) where
  mp := fun h g => .mp h g
  k := cd_16
  s := cd_106
  peirce := cd_25
  efq := certificate_exfalso

#print axioms certificate_classical
end SetTheory.BusyBeaver.ZFC.Tarski
