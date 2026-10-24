# Direct quartics with paired sign guards

Completed new endpoint: 489 unrestricted integers, exact degree 4,
308 squared quadratic residuals, 6905 monomials, height11302118.
Simpler endpoint: 493 unrestricted integers, degree 4, 310 residuals,
7174 monomials, height10945213. These improve the inherited 517-integer
factorial-carrier quartic, not the 11-variable higher-degree frontier.

Every variable and coefficient is explicit in the JSON equations and full
expanded polynomials. There are no hidden sign constraints, special-function
graphs or unspecified program constants. The existing ordinary C222/ZFC
calibration and signed-Pell correctness are inherited, not newly certified
in a proof-assistant kernel. The new reductions are proved in PROOF.md.

Attribution: the paired-product sign principle already appears in the
upstream six-anchor construction at commit 59ee8f21244635b42f706a74c4e9631226dd1f7c
(24 October 2026, 22:32 UTC). Its preserved review reports 1436 coordinates
and 1242 rows before projection, not our projected endpoint. Our concrete
contribution is twelve post-power pairs, measured 517->493 projection, and
the additional F² sign-anchor change giving 489. We claim no priority for
the underlying product-sign lemma. See inherited_proofs/late and PROOF.md.

Main results:
- Two signs with known nonnegative sum need only one product sign guard.
- The existing F² wire can make the factorial radius, endpoint and budget
  positive before F is interpreted, removing its separate sign guard.

Rebuild from the frozen included source, with standard-library Python only:

    python build_pairguards.py source paired
    python build_pairguards.py source squared_paired --squared-radius

Use -O as well. New certificates include the literal pair-sum identities,
all changed radius rows, fresh presemantic positivity derivations, exact
Horn-factorization identities, and monic projection/restoration maps.

The source equation is the derived16 square-shell direct C222 certificate
from ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24,
archived by ProveIt main at 45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6.
No remote state was changed.
