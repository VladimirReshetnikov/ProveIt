import Lean
/-! Are canonically-equivalent identifier spellings the same identifier? -/
open Lean

-- (1) bare NFC: é is U+00E9, inside `isLetterLike`'s Latin-1 range
def café : Nat := 1

-- (2) bare NFD: e + U+0301.  U+0301 is NOT in any isIdRest range.
def café : Nat := 2

-- (3) NFD inside French quotes, which accept arbitrary characters
def «café» : Nat := 3

-- (4) NFC inside French quotes
def «café» : Nat := 4
