prelude
import Init.Prelude
-- Which kernel-special-cased names does `Init.Prelude` leave FREE?
-- Anything reported as `unknown constant` is a name a downstream module may define,
-- while the kernel has already installed a hard-wired rule for it.
#check @Nat.add
#check @Nat.sub
#check @Nat.mul
#check @Nat.pow
#check @Nat.div
#check @Nat.mod
#check @Nat.beq
#check @Nat.ble
#check @Nat.gcd
#check @Nat.land
#check @Nat.lor
#check @Nat.xor
#check @Nat.shiftLeft
#check @Nat.shiftRight
#check @String.ofList
#check @Char.ofNat
#check @List.cons
#check @List.nil
#check @Lean.reduceBool
#check @Lean.reduceNat
#check @eagerReduce
