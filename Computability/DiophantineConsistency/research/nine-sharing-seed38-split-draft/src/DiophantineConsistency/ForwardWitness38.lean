import DiophantineConsistency.SharingGateModel

/-! UNCOMPILED DRAFT. A forward witness constructor generated from the exact
38-witness candidate. Its residual-correctness theorem and the all-model
reverse bridge have not yet been proved or checked. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingForward38

/-- Every cut witness is a semiring expression in earlier witnesses and inputs. -/
def witnessCoordinates {S : Type*} [CommSemiring S]
    (ports : Fin 4 → S) (u : Fin 14 → S) : Fin 38 → S :=
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
  let w26 : S := ((((ports 0) * ((u 0) + (1 : S))) * (((ports 0) * ((u 0) + (1 : S))) + (1 : S))) + ((u 2) + (1 : S)))
  let w27 : S := (((ports 0) * ((u 0) + (1 : S))) * ((u 1) + (1 : S)))
  let w28 : S := (((w19 * ((u 9) + (1 : S))) + (((u 10) + (1 : S)) + ((u 11) + (1 : S)))) + (w26 + (w27 * w15)))
  let w29 : S := (((w26 * w15) + w27) + (((ports 2) + ((((ports 0) * ((u 0) + (1 : S))) + (1 : S)) * (ports 3))) * ((u 0) + (1 : S))))
  let w30 : S := (((u 4) + (1 : S)) * ((u 4) + (1 : S)))
  let w31 : S := (((w20 + ((u 10) + (1 : S))) * ((u 6) + (1 : S))) + (w26 + (w27 * w15)))
  let w32 : S := (((w26 * w15) + w27) + (((ports 2) + ((((ports 0) * ((u 0) + (1 : S))) + (1 : S)) * (ports 3))) * ((u 0) + (1 : S))))
  let w33 : S := (w30 * w31)
  let w34 : S := ((w30 * w32) + (w20 + ((u 10) + (1 : S))))
  let w35 : S := (((u 5) + (1 : S)) * w25)
  let w36 : S := (w35 * w35)
  let w37 : S := ((w33 * w33) + (w34 * w34))
  let w38 : S := (((w33 * w34) + (w34 * w33)) + (((u 12) + (1 : S)) * ((u 12) + (1 : S))))
  ![u 0, u 1, u 2, u 3, u 4, u 5, u 6, u 7, u 8, u 9, u 10, u 11, u 12, u 13, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38]

end DiophantineConsistency.SharingForward38
