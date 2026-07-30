-- Five byte-distinct spellings.  Lean declares ONE constant.
-- lone high surrogate U+D800
def Â«Xí €YÂ» : Nat := 0
-- lone low surrogate U+DC00
def Â«Xí°€YÂ» : Nat := 1
-- raw 0xFF
def Â«XÿYÂ» : Nat := 2
-- overlong NUL
def Â«XÀ€YÂ» : Nat := 3
-- genuine U+FFFD (valid UTF-8!)
def Â«Xï¿½YÂ» : Nat := 4
