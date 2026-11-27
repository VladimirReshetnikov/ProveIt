import GRHArticle.SingularModuli.ReducedForms

/-!
# Degrees of the listed small class polynomials

The cubic list comes from `cm/verify_all_cubics.py` in the archived
`grh_sparse_singular_moduli` report. The quartic and quintic lists come
from `certificates/cm-all-polys.json` in `grh_cm_sparse_equations`,
both at revision `10802a6b36`. The degree checks recompute the primitive
reduced forms. Exhaustiveness among all discriminants requires the global
class-number bounds used in `smd:sec:small`.
-/

namespace GRHArticle.SingularModuli

/-- The 25 discriminant magnitudes in the article's cubic list. -/
def cubicDiscriminants : List ℕ+ :=
  [23, 31, 44, 59, 76, 83, 92, 107, 108, 124, 139, 172, 211, 243, 268, 283, 307, 331, 379,
   499, 547, 643, 652, 883, 907]

theorem cubicDiscriminants_length : cubicDiscriminants.length = 25 := by decide

theorem cubicDiscriminants_nodup : cubicDiscriminants.Nodup := by decide +kernel

theorem analyticClassPolynomial_natDegree_of_mem_cubic {D : ℕ+} (hD : D ∈ cubicDiscriminants) :
    (analyticClassPolynomial D).natDegree = 3 := by
  have hc : cubicDiscriminants.all (fun d => (reducedForms d).card == 3) = true := by
    decide +kernel
  rw [analyticClassPolynomial_natDegree]
  exact eq_of_beq (List.all_eq_true.mp hc D hD)

/-- The 84 discriminant magnitudes in the article's quartic list. -/
def quarticDiscriminants : List ℕ+ :=
  [39, 55, 56, 63, 68, 80, 84, 96, 120, 128, 132, 136, 144, 155, 156, 160, 168, 171, 180,
   184, 192, 195, 196, 203, 208, 219, 220, 228, 240, 252, 256, 259, 275, 280, 288, 291,
   292, 312, 315, 323, 328, 340, 352, 355, 363, 372, 387, 388, 400, 408, 435, 448, 475,
   483, 507, 520, 532, 555, 568, 592, 595, 603, 627, 667, 708, 715, 723, 760, 763, 772,
   795, 928, 955, 1003, 1012, 1027, 1227, 1243, 1387, 1411, 1435, 1467, 1507, 1555]

theorem quarticDiscriminants_length : quarticDiscriminants.length = 84 := by decide

theorem quarticDiscriminants_nodup : quarticDiscriminants.Nodup := by decide +kernel

theorem analyticClassPolynomial_natDegree_of_mem_quartic {D : ℕ+} (hD : D ∈ quarticDiscriminants) :
    (analyticClassPolynomial D).natDegree = 4 := by
  have hc : quarticDiscriminants.all (fun d => (reducedForms d).card == 4) = true := by
    decide +kernel
  rw [analyticClassPolynomial_natDegree]
  exact eq_of_beq (List.all_eq_true.mp hc D hD)

/-- The 29 discriminant magnitudes in the article's quintic list. -/
def quinticDiscriminants : List ℕ+ :=
  [47, 79, 103, 127, 131, 179, 188, 227, 316, 347, 412, 443, 508, 523, 571, 619, 683, 691,
   739, 787, 947, 1051, 1123, 1723, 1747, 1867, 2203, 2347, 2683]

theorem quinticDiscriminants_length : quinticDiscriminants.length = 29 := by decide

theorem quinticDiscriminants_nodup : quinticDiscriminants.Nodup := by decide +kernel

theorem analyticClassPolynomial_natDegree_of_mem_quintic {D : ℕ+} (hD : D ∈ quinticDiscriminants) :
    (analyticClassPolynomial D).natDegree = 5 := by
  have hc : quinticDiscriminants.all (fun d => (reducedForms d).card == 5) = true := by
    decide +kernel
  rw [analyticClassPolynomial_natDegree]
  exact eq_of_beq (List.all_eq_true.mp hc D hD)

end GRHArticle.SingularModuli
