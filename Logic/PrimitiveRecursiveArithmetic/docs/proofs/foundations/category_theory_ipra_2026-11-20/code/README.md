# Executable finite examples

Run with Python 3.10 or later, with no third-party packages:

```bash
python3 finite_models.py --json verification_results.json
```

The script exhaustively checks the indicated finite examples using exact
integers and tuples. It is **not** an iPRA proof checker, and finite testing
does not prove the general theorems.

## Encodings and cases

Maps `[n] → [m]` are tuples of `n` digits strictly below `m`. Their integer
codes use base `m+1`. Invalid table codes are rejected by a bounded digit
test. The unique empty table is accepted for every codomain. When `m=0<n`,
there are no tables. Exponential points are ranks in the increasing list of
valid table codes, with cardinality `m^n` and convention `0^0=1`.
The product point `(x,y) ∈ [n] × [m]` has code `m*x+y`, matching the report.

The run checks:

* table code/decode and table cardinalities for cardinalities through 3;
* product pairing/projection equations and uniqueness, and both exponential
  round trips, for all base parameters `n,m,z` from 0 through 3 (intermediate
  product and exponential cardinalities can be larger);
* full limit and colimit universal properties, with test object cardinalities
  through 3, for eight diagrams including the empty diagram, empty objects,
  empty equalizers, a pullback, a loop, and a coequalizer requiring transitive
  identifications;
* the complete set of natural transformations in Yoneda's lemma for two
  two-element monoids, one a group and one with a zero element;
* all 1,024 component families from `Hom(-,[2])` to the powerset presheaf on
  the full category of finite sets with cardinalities 0, 1, 2;
* identities and associativity of the option monad's Kleisli composition for
  object cardinalities through 2.

The report proves colimit correctness by sequential label merging. The
finite-colimit routine independently uses the literal bounded Warshall recurrence with
separate Boolean matrices at each stage, then least representatives and their
ranks. The universal-property checks enumerate all compatible cocones for
the stated test codomains, including the empty codomain. No random sampling,
floating point comparison, or solver assumptions are used.

The generated `verification_results.json` records the actual case counts.
