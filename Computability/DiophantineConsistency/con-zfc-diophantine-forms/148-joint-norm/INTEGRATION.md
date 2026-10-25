# Integration notes

The deliverable is self-contained for finite algebra checks and contains the retained ordinary proof dependencies used by its two constructions. The reference snapshot is commit `3ecd6a6cf53d47519228328567f45fb7ee9781d9`.

## Suggested placement

Preserve this directory as a new research package under `Computability/DiophantineConsistency/con-zfc-diophantine-forms`, using the next available package number or an unnumbered `joint-ceiling-norm` directory. The root archive can enter `docs/incoming` unchanged. Do not replace the earlier packages: their independent degree, operation, domain, and coefficient tradeoffs remain relevant.

## Main candidate

- Name: joint ceiling-and-digit norm, P245.
- Domain: unrestricted integers.
- Variables: 245.
- Residuals: 181 quadratic or affine integer polynomials.
- Exact total degree: 4.
- Collected support: 5,304 monomials.
- Coefficient height: 128,446.
- Definition: `direct/equation/equation.json`, with full expansion alongside it.
- New proof: `direct/proofs/BOOTSTRAP_PROOF.md` and the main article.
- Finite verification: `direct/code/verify.py`.

The new theorem is zero existence equivalent to finite ZFC refutability, using the inherited C222 and constructible-choice calibration. Keep its ordinary-proof status separate from the status of inherited Lean interfaces. The new source-edit verifier does not itself prove the unbounded semantics.

## Compact companion

- Name: staged main-square recovery.
- Domain: ten strictly positive integers.
- Exact degree: 454.
- Operations: 78, counting every live binary addition, subtraction, and multiplication, including scalar products and squares.
- Definition and proof: `compact/equation78_degree454.json` and `compact/PROOF.md`.
- Fixed constants: use the entire supplied tuple. No component is interchangeable with a different native-radix tuple.

## Suggested formalization units

1. A signed-base extension of the bounded Pell power congruence, for absolute base at least two.
2. The nearest-integer factorial identity for all t>=4, and its <1/32 canonical error bound for t>=16.
3. Centered signed congruence recovery with a common denominator.
4. The bootstrap order deriving |B|>=2, x>=t+1, and the representative signs without any initial front sign guard.
5. A local certificate checker for the quadratic source edit, followed by the existing monic projection and translation machinery.

For the compact branch, formalize the coprime product-square recovery and its ordered implication: E*Dm square, strong pair, main-index folding, Dm square, E square. Assuming E square before folding would make that argument circular.

The full formal compiler and object-language internalization remain separate tasks. The package supplies no new end-to-end Lean or Rocq proof term and does not assert consistency or actual unsolvability.
