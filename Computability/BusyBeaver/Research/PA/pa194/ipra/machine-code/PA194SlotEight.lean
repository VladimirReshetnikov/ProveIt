import M6.Source.PhysicalRegisters
/-! The finite source-to-physical register permutation used by the verified
PA194 file layout. This does not prove a machine/source simulation. -/
namespace PA194SlotEight
theorem logicalSixAtPhysicalEight : M6.Source.physicalRegister ⟨6,by decide⟩ = 8 := by decide
#print axioms logicalSixAtPhysicalEight
end PA194SlotEight
