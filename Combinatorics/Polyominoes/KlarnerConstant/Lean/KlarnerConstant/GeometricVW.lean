import KlarnerConstant.GeometricV
import KlarnerConstant.GeometricW

/-!
# Compatibility facade for the V and W geometric recurrences

The two developments are compiled separately to keep Lean's peak elaboration
state bounded. New code may import `GeometricV` and `GeometricW` directly;
this module preserves the original combined import surface.
-/
