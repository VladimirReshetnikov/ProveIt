From K230L Require Import Codes230.
From K215F Require Import DominatedImplication DomRho8 Thm222 ThmDom EnumPerm L1_CompPerm SeedPerm.
Check (@DomRho8.dtruth : forall T, DomRho8.DomImp T -> T 0).
Check (@DomRho8.dmp : forall T, DomRho8.DomImp T -> forall a b, T (wim a b) -> T a -> T b).
Check (@DomRho8.drho8 : forall T, DomRho8.DomImp T -> forall a b c u, u <= a -> T (Codes230.rho8 a b c u)).
Check (@DomRho8.rho8_all : forall T, DomRho8.DomImp T -> forall a b c u, T (Codes230.rho8 a b c u)).
Check (seedPerm_complete : thm222 1 -> halts_from seedPerm).
Check (seedPerm_sound : halts_from seedPerm -> thm222 1).
Check (seedPerm_iff_thm : halts_from seedPerm <-> thm222 1).
Print Assumptions DominatedImplication.rho8_all.
Print Assumptions DominatedImplication.composition.
Print Assumptions DominatedImplication.lift_right.
Print Assumptions DominatedImplication.basisK.
Print Assumptions DominatedImplication.basisPeirce.
Print Assumptions DominatedImplication.basisS.
Print Assumptions DomRho8.rho8_all.
Print Assumptions DomRho8.rho8_all_of_restricted.
Print Assumptions seedPerm_iff_thm.
