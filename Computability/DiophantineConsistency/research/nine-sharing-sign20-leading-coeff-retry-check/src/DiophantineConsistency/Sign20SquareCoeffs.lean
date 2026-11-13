import DiophantineConsistency.Sign20LeadingRows

/-! SOURCE-ONLY: twentieth coefficients of port-dependent axis squares. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20LeadingRows
open MvPolynomial

theorem dc2_square_coeff (z : ℤ) :
    MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 20)
      ((-(((X 0)*((X 0)+1)*((z : MvPolynomial (Fin 1) ℤ)*((X 0)+1)+1)+(X 0))^2 + 4*((X 0)*((X 0)+1)*((z : MvPolynomial (Fin 1) ℤ)*((X 0)+1)+1)+(X 0)) + 3) * ((X 0)^2+3*(X 0)+1)^2)^2 : MvPolynomial (Fin 1) ℤ) = z^4 := by
  have hc (v : ℤ) : (MvPolynomial.C v : MvPolynomial (Fin 1) ℤ) =
      (v : MvPolynomial (Fin 1) ℤ) := by
    exact map_intCast (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 1) ℤ) v
  have h : ((-(((X 0)*((X 0)+1)*((z : MvPolynomial (Fin 1) ℤ)*((X 0)+1)+1)+(X 0))^2 + 4*((X 0)*((X 0)+1)*((z : MvPolynomial (Fin 1) ℤ)*((X 0)+1)+1)+(X 0)) + 3) * ((X 0)^2+3*(X 0)+1)^2)^2 : MvPolynomial (Fin 1) ℤ) =
      MvPolynomial.C (z^4) * (X 0)^20 +
      MvPolynomial.C ((4 : ℤ) * z^3 + (20 : ℤ) * z^4) * (X 0)^19 +
      MvPolynomial.C ((6 : ℤ) * z^2 + (80 : ℤ) * z^3 + (182 : ℤ) * z^4) * (X 0)^18 +
      MvPolynomial.C ((4 : ℤ) * z + (120 : ℤ) * z^2 + (732 : ℤ) * z^3 + (1000 : ℤ) * z^4) * (X 0)^17 +
      MvPolynomial.C ((1 : ℤ) + (80 : ℤ) * z + (1104 : ℤ) * z^2 + (4072 : ℤ) * z^3 + (3713 : ℤ) * z^4) * (X 0)^16 +
      MvPolynomial.C ((20 : ℤ) + (740 : ℤ) * z + (6216 : ℤ) * z^2 + (15432 : ℤ) * z^3 + (9880 : ℤ) * z^4) * (X 0)^15 +
      MvPolynomial.C ((186 : ℤ) + (4216 : ℤ) * z + (24022 : ℤ) * z^2 + (42288 : ℤ) * z^3 + (19494 : ℤ) * z^4) * (X 0)^14 +
      MvPolynomial.C ((1072 : ℤ) + (16600 : ℤ) * z + (67648 : ℤ) * z^2 + (86712 : ℤ) * z^3 + (29100 : ℤ) * z^4) * (X 0)^13 +
      MvPolynomial.C ((4297 : ℤ) + (47952 : ℤ) * z + (143620 : ℤ) * z^2 + (135680 : ℤ) * z^3 + (33220 : ℤ) * z^4) * (X 0)^12 +
      MvPolynomial.C ((12712 : ℤ) + (105080 : ℤ) * z + (234248 : ℤ) * z^2 + (163560 : ℤ) * z^3 + (29100 : ℤ) * z^4) * (X 0)^11 +
      MvPolynomial.C ((28678 : ℤ) + (177856 : ℤ) * z + (296032 : ℤ) * z^2 + (152160 : ℤ) * z^3 + (19494 : ℤ) * z^4) * (X 0)^10 +
      MvPolynomial.C ((50188 : ℤ) + (234264 : ℤ) * z + (290008 : ℤ) * z^2 + (108656 : ℤ) * z^3 + (9880 : ℤ) * z^4) * (X 0)^9 +
      MvPolynomial.C ((68572 : ℤ) + (239936 : ℤ) * z + (218756 : ℤ) * z^2 + (58800 : ℤ) * z^3 + (3713 : ℤ) * z^4) * (X 0)^8 +
      MvPolynomial.C ((72988 : ℤ) + (189520 : ℤ) * z + (125248 : ℤ) * z^2 + (23588 : ℤ) * z^3 + (1000 : ℤ) * z^4) * (X 0)^7 +
      MvPolynomial.C ((59926 : ℤ) + (113616 : ℤ) * z + (53158 : ℤ) * z^2 + (6768 : ℤ) * z^3 + (182 : ℤ) * z^4) * (X 0)^6 +
      MvPolynomial.C ((37288 : ℤ) + (50404 : ℤ) * z + (16112 : ℤ) * z^2 + (1308 : ℤ) * z^3 + (20 : ℤ) * z^4) * (X 0)^5 +
      MvPolynomial.C ((17121 : ℤ) + (15920 : ℤ) * z + (3280 : ℤ) * z^2 + (152 : ℤ) * z^3 + z^4) * (X 0)^4 +
      MvPolynomial.C ((5576 : ℤ) + (3364 : ℤ) * z + (400 : ℤ) * z^2 + (8 : ℤ) * z^3) * (X 0)^3 +
      MvPolynomial.C ((1210 : ℤ) + (424 : ℤ) * z + (22 : ℤ) * z^2) * (X 0)^2 +
      MvPolynomial.C ((156 : ℤ) + (24 : ℤ) * z) * (X 0)^1 +
      MvPolynomial.C ((9 : ℤ)) * (X 0)^0 := by
    simp only [hc]
    ring
  rw [h]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_single_X_pow]
  norm_num

theorem n0_square_coeff (z : ℤ) :
    MvPolynomial.coeff (Finsupp.single (0 : Fin 1) 20)
      ((-((X 0)*((X 0)+1)*((z : MvPolynomial (Fin 1) ℤ)*((X 0)+1)+1)*(((X 0)+2)*(X 0))) * ((X 0)*((X 0)+1)*((z : MvPolynomial (Fin 1) ℤ)*((X 0)+1)+1)*(((X 0)+2)*(X 0))+((X 0)+2)) - 1)^2 : MvPolynomial (Fin 1) ℤ) = z^4 := by
  have hc (v : ℤ) : (MvPolynomial.C v : MvPolynomial (Fin 1) ℤ) =
      (v : MvPolynomial (Fin 1) ℤ) := by
    exact map_intCast (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 1) ℤ) v
  have h : ((-((X 0)*((X 0)+1)*((z : MvPolynomial (Fin 1) ℤ)*((X 0)+1)+1)*(((X 0)+2)*(X 0))) * ((X 0)*((X 0)+1)*((z : MvPolynomial (Fin 1) ℤ)*((X 0)+1)+1)*(((X 0)+2)*(X 0))+((X 0)+2)) - 1)^2 : MvPolynomial (Fin 1) ℤ) =
      MvPolynomial.C (z^4) * (X 0)^20 +
      MvPolynomial.C ((4 : ℤ) * z^3 + (16 : ℤ) * z^4) * (X 0)^19 +
      MvPolynomial.C ((6 : ℤ) * z^2 + (60 : ℤ) * z^3 + (116 : ℤ) * z^4) * (X 0)^18 +
      MvPolynomial.C ((4 : ℤ) * z + (84 : ℤ) * z^2 + (404 : ℤ) * z^3 + (504 : ℤ) * z^4) * (X 0)^17 +
      MvPolynomial.C ((1 : ℤ) + (52 : ℤ) * z + (522 : ℤ) * z^2 + (1614 : ℤ) * z^3 + (1462 : ℤ) * z^4) * (X 0)^16 +
      MvPolynomial.C ((12 : ℤ) + (296 : ℤ) * z + (1902 : ℤ) * z^2 + (4264 : ℤ) * z^3 + (2984 : ℤ) * z^4) * (X 0)^15 +
      MvPolynomial.C ((62 : ℤ) + (974 : ℤ) * z + (4536 : ℤ) * z^2 + (7874 : ℤ) * z^3 + (4396 : ℤ) * z^4) * (X 0)^14 +
      MvPolynomial.C ((182 : ℤ) + (2076 : ℤ) * z + (7536 : ℤ) * z^2 + (10516 : ℤ) * z^3 + (4712 : ℤ) * z^4) * (X 0)^13 +
      MvPolynomial.C ((343 : ℤ) + (3096 : ℤ) * z + (9187 : ℤ) * z^2 + (10450 : ℤ) * z^3 + (3649 : ℤ) * z^4) * (X 0)^12 +
      MvPolynomial.C ((462 : ℤ) + (3514 : ℤ) * z + (8730 : ℤ) * z^2 + (7996 : ℤ) * z^3 + (1992 : ℤ) * z^4) * (X 0)^11 +
      MvPolynomial.C ((507 : ℤ) + (3324 : ℤ) * z + (6886 : ℤ) * z^2 + (4914 : ℤ) * z^3 + (728 : ℤ) * z^4) * (X 0)^10 +
      MvPolynomial.C ((490 : ℤ) + (2714 : ℤ) * z + (4612 : ℤ) * z^2 + (2480 : ℤ) * z^3 + (160 : ℤ) * z^4) * (X 0)^9 +
      MvPolynomial.C ((395 : ℤ) + (1838 : ℤ) * z + (2533 : ℤ) * z^2 + (976 : ℤ) * z^3 + (16 : ℤ) * z^4) * (X 0)^8 +
      MvPolynomial.C ((260 : ℤ) + (1036 : ℤ) * z + (1120 : ℤ) * z^2 + (256 : ℤ) * z^3) * (X 0)^7 +
      MvPolynomial.C ((162 : ℤ) + (534 : ℤ) * z + (426 : ℤ) * z^2 + (32 : ℤ) * z^3) * (X 0)^6 +
      MvPolynomial.C ((90 : ℤ) + (236 : ℤ) * z + (136 : ℤ) * z^2) * (X 0)^5 +
      MvPolynomial.C ((34 : ℤ) + (74 : ℤ) * z + (24 : ℤ) * z^2) * (X 0)^4 +
      MvPolynomial.C ((16 : ℤ) + (24 : ℤ) * z) * (X 0)^3 +
      MvPolynomial.C ((8 : ℤ) + (8 : ℤ) * z) * (X 0)^2 +
      MvPolynomial.C ((1 : ℤ)) * (X 0)^0 := by
    simp only [hc]
    ring
  rw [h]
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_single_X_pow]
  norm_num
end DiophantineConsistency.Sign20LeadingRows
#print axioms DiophantineConsistency.Sign20LeadingRows.dc2_square_coeff
#print axioms DiophantineConsistency.Sign20LeadingRows.n0_square_coeff
