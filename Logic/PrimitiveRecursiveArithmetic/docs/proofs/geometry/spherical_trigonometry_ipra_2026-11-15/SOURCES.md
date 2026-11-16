# Sources and inspected interfaces

Access date for public web sources: **15 November 2026**.

## Requested formula sources

1. Wikipedia, “Spherical law of cosines”  
   https://en.wikipedia.org/wiki/Spherical_law_of_cosines
2. Wikipedia, “Law of sines — Spherical law of sines”  
   https://en.wikipedia.org/wiki/Law_of_sines#Spherical_law_of_sines
3. Wikipedia, “Half-side formula”  
   https://en.wikipedia.org/wiki/Half-side_formula
4. Wikipedia, “Law of cosines — Analogue for tetrahedra”  
   https://en.wikipedia.org/wiki/Law_of_cosines#Analogue_for_tetrahedra
5. Wikipedia, “Spherical trigonometry”  
   https://en.wikipedia.org/wiki/Spherical_trigonometry
6. Eric W. Weisstein, “Spherical Trigonometry,” MathWorld  
   https://mathworld.wolfram.com/SphericalTrigonometry.html

These pages were used as a formula-coverage checklist. Proofs in the packet are
independent derivations from vector identities, polar duality and constructive
trigonometric arithmetic.

## Classical and constructive references

- I. Todhunter, *Spherical Trigonometry*, 5th ed., Macmillan, 1886.
- Errett Bishop and Douglas Bridges, *Constructive Analysis*, Springer, 1985.
- Douglas Bridges and Fred Richman, *Varieties of Constructive Mathematics*,
  Cambridge University Press, 1987.

## ProveIt snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt  
Inspected commit: `a3c053cc6243dca44824510fac104958d616a6b9`

Principal interfaces and prior packets reused as specifications or proof
patterns:

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Syntax.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/Deduction.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/EqArith.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/BiInterpretation.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/trigonometric_identities_ipra_2026-11-15/`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/geometry/triangle_formulas_ipra/`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/geometry/euler_rodrigues_ipra/`

The repository’s `PR.lean` supplies the primitive-recursive symbol type,
`PRAAx`, and quantifier-free induction; `Deduction.lean` supplies scoped
intuitionistic first-order derivations with equality. The trigonometric packet
supplies the rapid-name and sine/cosine architecture; the triangle packet
supplies constructive planar sine/cosine-law patterns and bounded roots; the
Euler–Rodrigues packet supplies a reusable three-vector dot/cross polynomial
kernel.

## Validation tools

- Python 3 standard library plus SymPy 1.14.0 for exact generator checks.
- pdfTeX 1.40.26 / TeX Live 2025 development packages for the supplied PDF.
- PDF rendered for visual inspection at 150 dpi with the OpenAI PDF skill’s
  `render_pdf.py` utility.
