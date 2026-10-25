# Signed-network height-one quartics — Round18

Four complete coefficient-height-one quartics over unrestricted integers:

| Endpoint | Variables | Monomials | Source variables |
|---|---:|---:|---:|
| compact571 | 571 | 19,833 | 263 |
| balanced593 | 593 | 12,027 | 263 |
| sparse646 | 646 | 8,368 | 285 |
| sparser742 | 742 | 7,226 | 285 |

All have exact total degree 4, individual degree ≤ 4, constant coefficient 1,
and every nonzero collected coefficient equal to +1 or −1. Each polynomial is
nonnegative over the reals and its integer zero set is explicitly bijective
to that of its supplied signed quadratic source. The inherited source
calibration transfers the ZFC-provable equivalence between integer
unsolvability and Con(ZFC); this does not prove consistency.

The new construction reverses selected source rows, pairs identical monomials
with opposite signs, and replaces their two hub edges by one direct row-to-row
edge. Additional savings use coefficient-factor vertex covers and shorter
constant-definition chains. proof.tex gives the complete algebraic proof,
forward and inverse witness maps, uniqueness, and the correct signed off-zero
identity. Exact files in endpoints/ define the actual polynomials, not just
construction circuits.

## Replay

Python 3.10+ and its standard library suffice, without network or a source checkout:

    python verify.py --report replay.json

The default command runs both ordinary and optimized Python. It independently
checks all source pullbacks and occurrence boundaries, graph/tree invariants,
every coefficient through a half-sum-of-squares expansion, and the canonical
lift symbolically at every vertex. It parses each literal equation separately,
rejects 13 deliberate corruption classes per endpoint, and regenerates every
selected source transformation, certificate, and polynomial byte-for-byte.
Use --single for only the current interpreter; --skip-rebuild omits only the
producer rerun. Finite corruption tests supplement rather than replace the
unbounded proof.

The source proof interface is SOURCE_BINDINGS.json: the enclosing signed/
component supplies the new signed-source argument, and its retained Round17
proof closure supplies the underlying finite ZFC-refutation calibration.
The compact and balanced points improve both variables and terms over the
old 793/51,982 and 806/23,719 equations. Both sparse points improve both metrics
over the old 994/11,744 equation. These are selected tradeoffs, not an exhaustive
Pareto frontier or a global-optimality claim.

The matched-source replay in comparison/ isolates the compiler change: with
the identical prior refactored source and the same 48 hubs / seed 0, the prior
806-variable, 23,719-term equation becomes 603 variables and 12,289 terms.
This regenerated comparison is not an additional delivered endpoint.
The exact historical 806-variable polynomial, its certificate, its original
producer-free auditor, and the Round17 manifest are retained under comparison/.
The verifier checks their original hashes and independently reconstructs the
historical polynomial and witness lift. The historical manifest is a provenance
snapshot: only its explicitly retained comparison entries are required here.
