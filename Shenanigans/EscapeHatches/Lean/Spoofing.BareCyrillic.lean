-- Companion to Spoofing.lean section 3. MUST BE REJECTED: `Fаlse` below spells
-- the `a` as U+0430 CYRILLIC SMALL LETTER A, which Lean's `isIdRest` does not
-- admit. Expected: `error: expected token`, exit 1. Asserted by ../verify.ps1.
def Fаlse : Prop := True
