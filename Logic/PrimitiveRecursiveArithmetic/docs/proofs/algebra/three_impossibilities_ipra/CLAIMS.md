# Claims and trust boundary

| Claim | Status in this archive |
|---|---|
| Every valid straightedge-and-compass trace yields a finite quadratic tower | Fully argued in the paper, with explicit coordinate formulas and an iPRA implementation plan |
| `X^3 - 2` and `X^3 - 3X - 1` are irreducible over Q | Fully proved; independently checked by `scripts/finite_checks.py` |
| Cube doubling and trisection of 60 degrees are impossible | Fully derived from the quadratic-tower degree obstruction |
| The fixed primitive-recursive real `pi = 4 atan(1)` is the unit-disk area and satisfies `exp(i*pi) = -1` | Constructive proof developed in the paper; Lean implementation not included |
| A finite Hermite-Lindemann contradiction proves that no nonzero integer polynomial vanishes at `pi` | Human-readable proof developed with explicit auxiliary polynomials, integer bounds, prime selection, and final modular contradiction |
| Circle squaring is impossible | Derived from algebraicity of construction outputs and the preceding transcendence theorem |
| Completed Lean/ConciseIPRA derivation | **Not claimed** |
| `IPRAFormalizationBlueprint.lean` is a proof | **Not claimed**; milestone axioms expose the remaining dependency graph |
| Python checks prove the theorem | **Not claimed**; they check selected finite identities and inequalities only |

## External formalizations

A conventional Lean proof of `Transcendental Q Real.pi` and Mathlib's Lindemann analytical approximation were inspected as mathematical cross-checks. They are not imported as an object-level proof in iPRA. Their stronger ambient foundations must not be confused with the target `PRAAx` derivation.

## Reuse of ProveIt drafts

The current `docs/drafts` directory was surveyed and includes `FTA_iPRA.zip` and other related archives. Their binary contents were not unpacked or audited in this run, so this archive does not claim to have reused a theorem from them. The paper identifies `FTA_iPRA` as the natural integration point for the root-isolation milestone after audit.
