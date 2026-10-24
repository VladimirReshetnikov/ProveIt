# Parity and Pell witnesses for syntactic Con(ZFC)

Research contribution prepared for Vladimir Reshetnikov and ProveIt.
Release date: 23 October 2026, Pacific time.

**Main contribution:** a residue-controlled radical norm combines three
Pell witnesses without introducing false integer solutions. The final
fifteen-variable equation has exact degree **306** and a **139-operation**
integer arithmetic circuit. A shorter proof and lower-degree alternative
uses sixteen variables, degree **112**, and **119 operations**.

All variables in these statements range over **unrestricted integers**.
Registers are polynomial abbreviations, not additional unknowns.

The mathematical statement for each supplied equation is

    ZFC proves:
    (the equation has no integer solution) <=> Con(ZFC).

Here Con(ZFC) is syntactic absence of a finite refutation in the specified
ProveIt calculus. The new ordinary mathematical proofs establish two-way
existence equivalence to named calibrated predecessors. Composing with their
identified ordinary calibration theorems gives the displayed statement.
The packet does not assert consistency, prove unsolvability, or supply a new
end-to-end Lean/Rocq certificate or exported object-language ZFC derivation.
Finite exact checks do not replace the unbounded mathematical arguments.

## Read first

- `report/con-zfc-parity-norms.pdf`: complete research article.
- `report/con-zfc-parity-norms.tex`: standalone LaTeX source, with the direct
  normalization section already included.
- `CANDIDATES.json`: machine-readable metrics and exact artifact locations.
- `integer-norms/MOD4_PROOF.md`: final residue-class refinement.
- `integer-norms/PROOF.md`: the two-root and three-root recovery theorems.
- `integer-norms/UPSTREAM_PROOF.md` and `provenance/`: ordinary inherited
  calibration dependencies and their stated formalization boundaries.

The article's final appendix gives the entire recommended fifteen-variable
polynomial in one place. The earlier odd-sum versions remain in the packet
because their integrality argument is particularly transparent.

## Results and domain-matched comparisons

| Equation, all over Z | Variables | Exact degree | Live binary operations |
|---|---:|---:|---:|
| Incoming saturated unit-product | 16 | 184 | 135 |
| Incoming saturated sum of squares | 16 | 192 | 134 |
| **New modulus-four two-root norm** | **16** | **112** | **119** |
| **New modulus-four three-root norm** | **15** | **310** | **136** |
| **New centered modulus-four norm** | **15** | **306** | **139** |
| Incoming transport projection | 20 | 20 | 111 |
| **New scaled sign guard** | **20** | **18** | **115** |
| Incoming direct C222 quartic | 27,916 | 4 | — |
| **New direct C222 quartic** | **26,188** | **4** | — |

Each addition, subtraction, or multiplication costs one gate, including
squaring and multiplication by a constant. Fixed integer leaves and reuse
of a previous register cost no gates. This is an arithmetic-circuit measure,
not a bit-complexity or full coefficient-description-size measure.

For moderate degree and few variables, use
`integer-norms/equations/integer15_mod4_degree306.json`.
For a shorter recovery argument and much lower degree, use
`integer-norms/equations/integer16_mod4_degree112.json`.
The degree-310 fifteen-variable form saves three arithmetic operations.

This is not a fewest-variable or global optimality claim. Existing
nine-positive-variable and ten-unrestricted-variable equations remain
separate, much-higher-degree alternatives. The comparison is to the exact
repository snapshot and incoming archives identified below.

## The main mathematical idea

A bare norm of three radicals can vanish because two irrational radicals
cancel; it does not by itself recover three integer roots. In the present
parent, one already has

    A = 1 + m(m+1)k^2 = 1 mod 4,
    S^2 >= 4A > A.

Encode the signed sum of roots of

    A,  Q/c^4,  16 S^2 (Q V^2 - 1)/(Q - 1)

by a polynomial coordinate L congruent to 2 modulo 4. The first root is an
odd integer if rational. The third is a multiple of four if rational:
the inherited adjacent-coefficient Pell descent forces its normalized
rational root to be integral. A partial irrational cancellation would
leave either an odd integer or a multiple of four, neither of which is L.
The remaining pair cannot cancel because of the size separation.

The proof treats negative and zero radicands, zero denominators, root signs,
and the converse witness construction explicitly. The rational expressions
occur only in the proof. Every supplied equation and evaluator is
division-free.

The finalizer is (1+G)(1+N)-1, with G a sum of two squares. Integer units
force G=N=0. No nonnegativity claim about the radical norm N is needed.
A polynomial translation of the new coordinate then lowers exact degree
from 310 to 306. Full weighted expansions and nonzero actual-coefficient
certificates verify the cancellations.

## A separate direct proof-calculus result

`direct-quartic/` contains a complete polynomial that does not encode a
Turing-machine execution and does not use Jones' universal polynomial.
Its incoming predecessor already established that architecture. Our change
removes a redundant truncated-difference certificate in all 108 power
graphs, using a strict inequality already implied by their Pell equation.

| Literal expanded polynomial | Variables | Degree | Nonzero monomials |
|---|---:|---:|---:|
| Nonnegative integers | 14,956 | 4 | 670,455 |
| Unrestricted integers | 26,188 | 4 | 724,768 |

The integer form saves 1,728 variables relative to the completed incoming
27,916-variable form. Its largest absolute coefficient is
320,307,372,009,864. The JSON files contain every monomial and ordinary
integer coefficient, not an unexecuted instruction to construct them.

The direct component retains the complete upstream ordinary audit, the
exact pinned Lean source excerpts used for provenance, the new
normalization proof, and seven exact audit programs. Those source excerpts
are not advertised as a standalone Lean project or a completed kernel build.

## Exact coefficients and file formats

The small equations use the authentic six fixed source-34 integers beta,
K0, MC, MF, cone_A, cone_B. Complete compressed byte payloads and a finite
construction recipe are included. Their total raw length is 615,883 bytes.
MF already includes its inherited beta shift. All six are fixed
numerals, not quantified parameters. Hashes authenticate the bytes; the
bytes and recipe define the coefficients.

`integer-norms/equations/*.json` gives variable order, ordered polynomial
registers, fully inlined residuals, the final single polynomial, and its
degree certificate. `integer-norms/circuits/*.json` gives all binary gates.
No variable powers, factorials, undecided program indices, or hidden
quantifiers remain in these polynomial definitions.

The expanded direct JSON format stores a term as
`[integer_coefficient, list_of_variable_indices]`. Indices are zero-based;
repeated indices denote powers, and the empty list denotes the constant.

## Reproduce

Python 3.10 or later and the standard library suffice for all arithmetic
checks. No network, proof search, or symbolic algebra package is required.
From the extracted directory:

    python3 verify.py

This authenticates every release file against `MANIFEST.json`.

    python3 verify.py --replay

This first authenticates the release, then rebuilds and checks all three
components in a temporary copy. It checks the six main norm equations and
the twenty-variable equation in normal and optimized Python, rebuilds the
entire direct polynomial, and compares the regenerated finite artifacts
against the release. The release files themselves are not modified.
Detailed subprocess logs are printed only on failure.

Component commands are also usable independently:

    python3 integer-norms/build.py
    python3 integer-norms/check.py
    python3 -O integer-norms/check.py
    python3 integer20/build.py
    python3 integer20/check.py
    python3 -O integer20/check.py
    python3 direct-quartic/replay.py

PDFLaTeX with standard TeX Live packages rebuilds the article:

    python3 build_report.py --output ../rebuilt-parity-report.pdf

The script uses no shell escape and builds in a temporary directory.
PDF byte-for-byte equality across different TeX distributions is not
required. The delivered PDF has been rendered and visually inspected.

## Provenance and proof boundary

Reviewed repository: `VladimirReshetnikov/ProveIt`.
Final snapshot: `43ac596e36c105a0e8b07c2d1f5ae200cae9c056`.
Initial connector reads used `bf2f392d73eb2ed74bd51cfdb509ecb704d04eb3`.
`provenance/SNAPSHOT.json` records the incoming archive hashes.

The small-equation predecessor is the integer component of
`ConZFC_Saturated_Certificates_2026-10-24.zip`. The direct predecessor is
`ConZFC_Direct_Centered_Round12_2026-10-24.zip`. The twenty-variable result
uses the active joint22-centered construction. Their source notices,
licenses, coefficient bindings, and ordinary proof dependencies are retained.

The new proofs and independent internal reviews were AI-assisted, not
externally peer-reviewed. No worldwide priority claim is made. The concrete
deliverables are finite equations, two-way mathematical witness reductions,
exact degree and circuit certificates, and a smaller complete direct quartic.

