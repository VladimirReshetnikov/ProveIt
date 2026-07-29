#!/usr/bin/env python3
"""Regenerate the byte-exact .lean files in this directory.

They cannot be edited in a text editor: the whole point is that they contain
byte sequences that are not valid UTF-8, which an editor would silently repair.
"""
import pathlib
d = pathlib.Path(__file__).parent
LONE_HI   = b'\xed\xa0\x80'   # lone HIGH surrogate U+D800, WTF-8 encoded
LONE_LO   = b'\xed\xb0\x80'   # lone LOW  surrogate U+DC00
RAW_FF    = b'\xff'           # not a legal UTF-8 lead byte at all
OVERLONG  = b'\xc0\x80'       # overlong encoding of U+0000
REAL_FFFD = b'\xef\xbf\xbd'   # genuine U+FFFD - perfectly valid UTF-8
Q0, Q1    = b'\xc2\xab', b'\xc2\xbb'   # « »

parts = [("lone high surrogate U+D800", LONE_HI), ("lone low surrogate U+DC00", LONE_LO),
         ("raw 0xFF", RAW_FF), ("overlong NUL", OVERLONG),
         ("genuine U+FFFD (valid UTF-8!)", REAL_FFFD)]
out = b'-- Five byte-distinct spellings.  Lean declares ONE constant.\n'
for i, (label, b) in enumerate(parts):
    out += b'-- ' + label.encode() + b'\ndef ' + Q0 + b'X' + b + b'Y' + Q1 + b' : Nat := ' + str(i).encode() + b'\n'
(d/"collide.lean").write_bytes(out)

(d/"silent.lean").write_bytes(
  b'-- A theorem about a string literal that got corrupted in transit ...\n'
  b'theorem claim : "a' + LONE_HI + b'b".length = 3 := rfl\n'
  b'-- ... is literally the same theorem as this one:\n'
  b'theorem claim2 : "a' + REAL_FFFD + b'b".length = 3 := rfl\n'
  b'-- and the two literals are definitionally equal:\n'
  b'example : ("a' + LONE_HI + b'b" = "a' + REAL_FFFD + b'b") := rfl\n')

(d/"probe.lean").write_bytes(
  b'def sur : String := "' + LONE_HI + b'"\n'
  b'#eval sur.utf8ByteSize          -- 3: the string is now EF BF BD\n'
  b'#eval sur.length                -- 1\n'
  b'#eval sur.toList.map (fun c => c.toNat)   -- [65533] = U+FFFD\n')
print("regenerated")
