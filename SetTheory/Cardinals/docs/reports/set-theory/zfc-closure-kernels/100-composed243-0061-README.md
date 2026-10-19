# Finite total algebra certificates for finite ground clauses

This is a separate research direction for a future small consistency-search
frontend. It does not change the current small TM or establish a state saving.
The generic finite-stage theorem is standard; the contribution here is its
explicit application interface, integer certificate codec, and cost comparison.

## Files and reproduction

- `finite_algebra.tex`: ready-to-include report section with the exact finite
  bound, its proof, the unbounded consistency-search argument, costs, and scope.
- `finite_algebra.py`: standalone Python reference checker, requiring only the
  standard library.
- `finite_algebra_results.json`: saved exact finite controls and witnesses.

Run:

```sh
python3 finite_algebra.py --output finite_algebra_results.json
```

To use the checker from Python:

```python
from finite_algebra import GroundStage, eq, term
c, d = term("c"), term("d")
f = lambda x: term("f", x)
stage = GroundStage([(eq(c, d),), (eq(f(c), f(d), False),)])
assert stage.decide()["status"] == "UNSAT"
```

The carrier bound is exactly `max(1, number of distinct ground subterms)`.
The candidate integer enumerates total operation tables and predicate tables;
equality is equality of resulting carrier values. Only the explicitly listed
GROUND clauses are evaluated. Universally closing them over the finite carrier
would make the consistency-search argument wrong for theories with only
infinite models.

The reference intentionally has no fuel-based UNSAT verdict or catch-all
exception handler. An execution failure is not a refutation. Its abstract
finite loop is total with unbounded storage; real host capacity is not assumed
adequate for arbitrary stages.

## Audit of the existing equality-free path

The current ProveIt notes show that removing equality rows from the compact
Hilbert engine also removes required cross-variable instantiation. The reduced
CP/GIC compiler is validated by a PA-definable finite-sort countermodel with
the target false. Same-variable UI, primitive Bottom, fresh/injective renaming,
and signed atomic UI do not settle the missing composite colliding cases.
Thus this note does not propose deleting those rows from the existing machine.
It changes the entire finite refutation interface instead.

## Sources read

- Jeff Ketchersid's upstream m254 theory and proof-layer descriptions:
  <https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/design/settheory.md>
  and <https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/README.md>.
- Existing equality-free bisimulation route:
  <https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/BusyBeaver/Research/ZFC/equality_free_bisimulation.md>.
- Existing finite-sort obstruction and logical engine audit:
  <https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/BusyBeaver/Research/ZFC/typed_countermodel.md>
  and <https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/BusyBeaver/Research/ZFC/logical_engine_completeness.md>.
- Existing finite quotient certificate interface and retained signature:
  <https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/BusyBeaver/Research/ZFC/finite_quotient_frontend.md>
  and <https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/BusyBeaver/Research/ZFC/finite_quotient_frontend.py>.
- Stephen Cook, *Herbrand Theorem, Equality, and Compactness*, course notes:
  <https://www.cs.toronto.edu/~sacook/csc438h/notes/page39.pdf>.
- Samuel R. Buss, *On Herbrand's Theorem*:
  <https://math.ucsd.edu/~sbuss/ResearchWeb/herbrandtheorem/paper.pdf>.
- William McCune, Mace4's official finite-structure documentation:
  <https://www.cs.unm.edu/~mccune/prover9/manual/2009-02A/mace4.html>.

No global novelty is claimed for finite algebra enumeration or the small-model
argument. No exact FC15/FC16 native generator or binary TM compilation is
supplied here. The current padded-term frontend and this ordinary unpadded
signature require an explicit adapter before their finite stages can be
identified.
