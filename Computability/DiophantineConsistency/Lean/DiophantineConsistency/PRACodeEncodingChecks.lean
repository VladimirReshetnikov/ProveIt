import DiophantineConsistency.PRACodeEncoding

set_option autoImplicit false
namespace DiophantineConsistency.PRACodeEncodingChecks
open PRAFiniteFunctionCodes PRACodeEncoding

example {n : ℕ} (c : Code n) : decodeCode n (encodeCode c) = some c :=
  decodeCode_encodeCode c
example {n : ℕ} : Encodable (Code n) := inferInstance
-- A unary outer function cannot be composed with an empty argument list.
example : parse (.node (.leaf 3) (.node (.leaf 1) (.node (.leaf 5) (.leaf 0)))) = none := rfl
-- The successor symbol has arity one and is rejected at arity two.
example : decodeCode 2 (encodeCode Code.succ) = none := by
  simp [decodeCode, encodeCode, decode_encode, parse_code]
-- A projection index equal to its arity is out of range.
example : parse (.node (.leaf 2) (.node (.leaf 2) (.leaf 2))) = none := rfl

#print axioms decode_encode
#print axioms parse_code
#print axioms parse_codes
#print axioms decodeCode_encodeCode
end DiophantineConsistency.PRACodeEncodingChecks
