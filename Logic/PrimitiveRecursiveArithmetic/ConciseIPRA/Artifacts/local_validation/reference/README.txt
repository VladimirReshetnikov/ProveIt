Pinned upstream reference material
=================================
Repository: VladimirReshetnikov/ProveIt
Commit: e0d702b905c74b74a23d045f8289b151bb8ebcff
Root: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

upstream_base.tex = docs/Article/chapters/ch01_base.tex
upstream_certificates.tex = docs/Article/chapters/ch11_cert.tex
NativeBiInterpretation.lean = Lean/ConciseIPRA/NativeBiInterpretation.lean

These are unchanged reference sources under the supplied upstream license.
The article fragments use their original preamble and are not intended to
compile separately. The Lean file identifies the exact inherited theorems;
it imports the rest of the upstream Lean project, which is not bundled.
No fresh Lean build or formal verification of Python is claimed.
The self-contained new report compiles from ../report.tex.
