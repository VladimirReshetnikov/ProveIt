import DiophantineConsistency.SharingGateModel

/-! UNCOMPILED DRAFT. A forward witness constructor generated from the exact
52-witness candidate. Its residual-correctness theorem and the all-model
reverse bridge have not yet been proved or checked. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingForward52

/-- Every cut witness is a semiring expression in earlier witnesses and inputs. -/
def witnessCoordinates {S : Type*} [CommSemiring S]
    (ports : Fin 4 → S) (u : Fin 14 → S) : Fin 52 → S :=
  let w15 : S := ((((ports 0) * ((u 0) + (1 : S))) + (1 : S)) * (((ports 0) * ((u 0) + (1 : S))) + (1 : S)))
  let w16 : S := (w15 * (((ports 0) * ((u 0) + (1 : S))) + (1 : S)))
  let w17 : S := (((u 8) + (1 : S)) * (((ports 0) * ((u 0) + (1 : S))) + (1 : S)))
  let w18 : S := (((u 7) + (1 : S)) * w16)
  let w19 : S := (w17 * w18)
  let w20 : S := ((((u 10) + (1 : S)) + ((u 11) + (1 : S))) * w18)
  let w21 : S := (w19 * w20)
  let w22 : S := (((w19 + w18) * (w19 + w18)) + (((4 : S) * (w19 + w18)) + (3 : S)))
  let w23 : S := ((w17 + ((w19 + w18) * (w20 + ((u 10) + (1 : S))))) + (((u 13) + (1 : S)) * (((4 : S) * (w19 + w18)) + (3 : S))))
  let w24 : S := ((w20 + ((u 10) + (1 : S))) * (w20 + ((u 10) + (1 : S))))
  let w25 : S := (w22 * w24)
  let w26 : S := (w23 * w23)
  let w27 : S := ((((ports 0) * ((u 0) + (1 : S))) * (((ports 0) * ((u 0) + (1 : S))) + (1 : S))) + ((u 2) + (1 : S)))
  let w28 : S := (((ports 0) * ((u 0) + (1 : S))) * ((u 1) + (1 : S)))
  let w29 : S := (((w19 * ((u 9) + (1 : S))) + (((u 10) + (1 : S)) + ((u 11) + (1 : S)))) + (w27 + (w28 * w15)))
  let w30 : S := (((w27 * w15) + w28) + (((ports 2) + ((((ports 0) * ((u 0) + (1 : S))) + (1 : S)) * (ports 3))) * ((u 0) + (1 : S))))
  let w31 : S := ((w29 * w29) + (w30 * w30))
  let w32 : S := (((w29 * w30) + (w30 * w29)) + (w21 * (w21 + (((u 10) + (1 : S)) + ((u 11) + (1 : S))))))
  let w33 : S := ((((ports 1) + ((u 8) + (1 : S))) * (((ports 0) * ((u 0) + (1 : S))) + (1 : S))) + (((ports 0) * ((u 0) + (1 : S))) + (1 : S)))
  let w34 : S := (((((ports 1) + ((u 8) + (1 : S))) * (((u 1) + (1 : S)) + ((u 2) + (1 : S)))) + ((u 1) + (1 : S))) + (((u 3) + (1 : S)) * ((ports 0) * ((u 0) + (1 : S)))))
  let w35 : S := (((u 4) + (1 : S)) * ((u 4) + (1 : S)))
  let w36 : S := (((w20 + ((u 10) + (1 : S))) * ((u 6) + (1 : S))) + (w27 + (w28 * w15)))
  let w37 : S := (((w27 * w15) + w28) + (((ports 2) + ((((ports 0) * ((u 0) + (1 : S))) + (1 : S)) * (ports 3))) * ((u 0) + (1 : S))))
  let w38 : S := (w35 * w36)
  let w39 : S := ((w35 * w37) + (w20 + ((u 10) + (1 : S))))
  let w40 : S := (((u 5) + (1 : S)) * w25)
  let w41 : S := (w40 * w40)
  let w42 : S := ((w38 * w38) + (w39 * w39))
  let w43 : S := (((w38 * w39) + (w39 * w38)) + (((u 12) + (1 : S)) * ((u 12) + (1 : S))))
  let w44 : S := ((w41 * w42) + (((u 12) + (1 : S)) * ((u 12) + (1 : S))))
  let w45 : S := (w41 * w43)
  let w46 : S := (w22 * w35)
  let w47 : S := ((w31 * w26) + (w32 * w25))
  let w48 : S := ((w31 * w25) + (w32 * w26))
  let w49 : S := ((w47 * w44) + (w48 * w45))
  let w50 : S := ((w47 * w45) + (w48 * w44))
  let w51 : S := ((w49 * w33) + (w50 * w34))
  let w52 : S := ((w49 * w34) + (w50 * w33))
  ![u 0, u 1, u 2, u 3, u 4, u 5, u 6, u 7, u 8, u 9, u 10, u 11, u 12, u 13, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52]

end DiophantineConsistency.SharingForward52
