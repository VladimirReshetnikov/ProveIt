import DirectMainProjection

/-! Conditional algebra for transporting a direct balance into the old
main-congruence shape. This does not establish the balance from a graph. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectMainTransfer

/-- The compensating `H*w` changes the congruence witness, not the Pell root. -/
theorem transfer {V : Type*} [CommSemiring V] (U X a c H G R k main w : V)
    (hroot : U*(X+a*c)+H*(U*G+R+1)=H*k+U*main) :
    H*(U*w+R+1)+U*(X+a*c+H*G)=H*k+U*(main+H*w) := by
  calc
    H*(U*w+R+1)+U*(X+a*c+H*G) =
        U*(X+a*c)+H*(U*G+R+1)+U*(H*w) := by ring
    _ = H*k+U*main+U*(H*w) := by rw [hroot]
    _ = H*k+U*(main+H*w) := by ring

/-- The 91-style substitutions imply the needed old contribution identity. -/
theorem old_contribution {V : Type*} [CommSemiring V] (q s w : V) :
    ((q*w)*(q^3*s))*q=(q^5*s)*w := by ring

#print axioms DirectMainTransfer.transfer
#print axioms DirectMainTransfer.old_contribution
end DirectMainTransfer
