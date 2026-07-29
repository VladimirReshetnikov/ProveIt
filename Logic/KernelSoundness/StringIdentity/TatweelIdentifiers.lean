import Lean
open Lean

def foo : Nat := 1

-- (1) bare TATWEEL suffix: U+0640 is in none of `isLetterLike`'s ranges
def fooـ : Nat := 2

-- (2) bare TATWEEL prefix
def ـfoo : Nat := 3

-- (3) French-quoted suffix
def «fooـ» : Nat := 4

-- (4) French-quoted prefix
def «ـfoo» : Nat := 5
