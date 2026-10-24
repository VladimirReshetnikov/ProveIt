# Saturated positive Pell certificates

Research component for Vladimir Reshetnikov's ProveIt project, based on
repository commit `c1a102936aca437e9999530a0111e6ddab56dc6d`.

| Literal polynomial | Domain | Unknowns | Exact degree | Live binary operations |
|---|---|---:|---:|---:|
| `saturated_positive.json` | positive integers |9|1,628,768|434|
| `saturated_natural.json` | natural numbers |9|1,628,768|441|
| `saturated_radical_positive.json` | positive integers |9|1,103,950|1,074|
| `saturated_radical_natural.json` | natural numbers |9|1,103,950|1,081|

The unknown order is `b,g,h,s,w,C,i,j,n`. Every intermediate register is a
polynomial abbreviation. The natural j supplies the positive j-1; every other
natural coordinate supplies its successor. All fixed leaves are literal
integer payloads with complete finite reconstruction from the supplied
1,294-digit seed. No input-dependent powers or divisions occur in the equations.

`PROOF.md` contains the complete new mathematical reduction; `section.tex`
is its report-ready LaTeX component. The parent source/calibration and licensing
documents are retained under `provenance/`. Their historical relative references
do not claim to vendor the entire upstream repository.

## The mathematical change

Replace

    F_old=1+(A^2-1)D^2(iJC^2)^2

by

    F_new=1+(A^2-1)D(iJC^2)^2.

The factors D,F,I still become pairwise coprime squares. The proof-only square
root of D supplies a Pell ordinate, and index congruences recover exactly the
required original index. Completeness has an explicit finite-matrix-period
construction, and also the map i_new=sqrt(D)i_old. This is not a casual
polynomial identity between old and new F.

The small circuit uses the strict polynomial majorant T=A D i J C^2. The
lower-degree circuit uses a 333-term majorant of the complete saturated radical,
certified by 36,309 positive shifted defect coefficients. The uncorrected formal
square-root truncation is demonstrably invalid and is kept as a negative control.

## Reproduction

Python's standard library suffices. From this directory:

```sh
python3 verify.py
python3 -O verify.py
python3 reconstruct_fixed.py
python3 -O reconstruct_fixed.py
```

`verify.py` uses a separately implemented exact sparse polynomial ring. It
checks the source prefix structurally, local formulas, radical tables and
positive-coefficient identities, final norm, whole natural translation,
topology, liveness, counts, fixed hashes, exact resolved degrees and negative
controls. It does not import the circuit builders or discovery code.

`reconstruct_fixed.py` invokes the retained unmodified repository tool with
explicit in-archive seed/reference paths. It reconstructs all four native ports
from the seed and then all eleven live leaves from their exact recipes,
comparing complete decompressed bytes and signs. It performs no network access.
The preserved source itself is pinned in `SOURCE_PINS.json`.

To regenerate the authored local tables and literal graphs:

```sh
python3 discover_radical.py
python3 build.py
python3 build_radical.py
python3 verify.py
```

The discovery recurrence is exact rational arithmetic. It is not evaluated at
the polynomial's witness inputs. The delivered graphs are division-free.

## Proof boundary

The new unbounded Pell representation, finite-period witness construction,
uniform majorants and zero-existence transformations are proved in the article.
The native source/compiler and its equivalence to a syntactic ZFC refutation
remain explicitly inherited interfaces. The intended ordinary theorem is
formalizable in ZFC through those interfaces. This component supplies no new
end-to-end Lean/Rocq or encoded internal-ZFC derivation. Finite replay does not
prove Con(ZFC) and is not used as a substitute for the unbounded argument.

The first positive equation improves the frozen H2082 parent's 440 operations
and degree 1,845,940. The second improves both measured values of the incoming
direct-majorant endpoint (1,753 operations and degree 1,158,228), using the
different complete compact54-sharp source tuple. No global minimum or historical
priority is claimed. Fixed-leaf raw bytes and the smaller four-port raw bytes
are reported separately; neither is a variable count.

Retain the original notices in `provenance/`, especially its `licenses/` folder.
All coefficient ports are kept together; MF_source is already shifted once.
