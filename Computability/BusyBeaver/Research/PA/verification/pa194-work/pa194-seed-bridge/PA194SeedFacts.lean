import PA194SeedBridge
set_option autoImplicit false
set_option maxRecDepth 65536
namespace PA194SeedFacts
open M6.Source PA194SeedBridge

theorem file_length : seedFile.length = 35 := by decide +kernel

theorem logical_seed : ∀ r : Fin 9,
    readFile seedFile r = if r.val = 0 then 2 else 0 := by decide +kernel

#print axioms file_length
#print axioms logical_seed
end PA194SeedFacts
