# Sign20 syntax and squares source-only draft

Generated from the pinned independently reviewed sign20 external AST. The
author parser checks residual transcription only; no Lean compilation or
all-model bridge is asserted. Coordinate zero is an unused input coordinate
and the 20 witnesses occupy Fin21 indices 1 through 20.

`Sign20Coordinate.lean` is a separate uncompiled sketch for eliminating the
old E coordinate at index 16. Its model beta is supplied explicitly, with a
hypothesis identifying it with the image of port zero. It requires guarded
compilation and independent review before any coordinate claim is made.
