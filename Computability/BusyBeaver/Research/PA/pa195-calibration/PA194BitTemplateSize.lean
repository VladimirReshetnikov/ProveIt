import PA194BitTemplate

/-! Executable size observation for the concrete generated function-code AST.
The `#eval` result is an evaluation, not a kernel-checked size theorem. -/
set_option autoImplicit false
namespace PA194BitTemplateSize
open DiophantineConsistency.PRAFiniteFunctionCodes

mutual
  def codeSize : {n : Nat} → Code n → Nat
    | _, .zero _ => 1
    | _, .succ => 1
    | _, .proj _ => 1
    | _, .comp f g => 1 + codeSize f + codesSize g
    | _, .prec f g => 1 + codeSize f + codeSize g
  def codesSize : {n m : Nat} → Codes n m → Nat
    | _, _, .nil _ => 1
    | _, _, .cons h t => 1 + codeSize h + codesSize t
end

#eval codeSize PA194BitTemplate.bitTemplateCode
end PA194BitTemplateSize
