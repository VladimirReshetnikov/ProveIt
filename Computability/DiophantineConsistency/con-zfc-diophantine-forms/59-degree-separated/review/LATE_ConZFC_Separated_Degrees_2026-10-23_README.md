# Separated degrees and Pell quotients

Explicit smaller Diophantine consistency equations for ProveIt, prepared on
2026-10-23 against repository revision
`4b4349064a750ba6347293b55874a7f92abdd0db`.

Start with **`report/main.pdf`**. Its complete LaTeX sources are in `report/`.
The polynomial definitions, all fixed coefficients, proofs, independent
checkers, source pins, and attribution are included in this directory.

## Results

Each listed equation has a zero in its stated domain exactly when there is
a finite syntactic ZFC refutation, by the new mathematical reductions and
the named inherited native-compiler/K215 calibration theorems. Negation gives
the ZFC-provable consistency equivalence. This is an ordinary mathematical
proof with explicit dependencies; no new end-to-end Lean/Rocq certificate or
object-language `BProv` derivation is claimed.

| Domain | Unknowns | Exact total degree | Binary operations | Polynomial file |
|---|---:|---:|---:|---|
| Positive integers | 12 | **242** | **94** | `low_degree/twelve_positive_degree242.json` |
| Positive integers | 12 | **258** | **89** | `low_degree/twelve_positive_degree258.json` |
| Positive integers | 13 | 132 | 83 | `low_degree/thirteen_positive_degree132.json` |
| Positive integers | 9 | **2,628,944** | **499** | `generated/nine_positive.json` |
| Nonnegative integers | 9 | 2,628,944 | 501 | `generated/nine_natural.json` |
| Unrestricted integers | 10 | **8,317,400** | **544** | `generated/ten_integer.json` |
| Unrestricted integers | 45 | **4** | Not optimized | `quartic/quartic45.json` |

The 45-integer equation is the sum of squares of 28 explicitly listed
quadratic residuals. Its exact expansion has 407 symbolic terms. A dominated
but transparent twelve-positive intermediate, degree 314 and 91 operations,
is also included.

The recommended balanced positive equation is the degree-242 form. Its
degree is 73.02% below the incoming twelve-positive degree-897 form, while
using 94 rather than 108 operations. The degree-258 form uses only 89.
The nine-positive and ten-integer forms improve both the smallest degree
and the smallest operation count found at those domain/variable counts,
even though the two baseline minima come from different incoming equations.
See `proofs/WAVE7_AUDIT.md` for all eight inspected archives. No absolute
minimality or improvement at every tradeoff is claimed.

## New mechanisms

1. **Separate ordinary degrees inside one packed word.** The source is
   `A2(B)y^2 + A1(B)y + A0(B) + B^1915(y^2+1)`, with
   `y=g+sum(B^w_i)`. Cross-degree collisions are harmless. A finite symbolic
   certificate checks all 23,599 relevant interactions and reconstructs
   all 22 source residuals. The carrier is positive for every integer `y`,
   before any encoded-witness bound is recovered.
2. **Two separate quadratic norms.** The direct positive construction removes
   three Pell witnesses and an index quotient while recovering their signs
   and exact indices in a noncircular order.
3. **Use a Pell ordinate's known residue.** Canonical witnesses have
   `y_old = -1 mod Q`. Substituting `y_old=M*y-1` and removing a fixed
   polynomial factor gives degrees 258 and 242. Both directions are proved;
   this is an existential coordinate change, not a universal restriction on
   every old witness.
4. **Share positivity information.** The quartic uses a dyadic guard for its
   radix and product guards for three quantities whose sum is positive.
   A formerly guarded transport quotient is recovered later from the
   arithmetic equations. This saves five integer unknowns.

The precise inheritance of earlier carry padding, mask-population
calibration, CRT reparameterization, Pell majorants, and Sun finalizers is
recorded in `NOTICE.md`. Those earlier ideas are not claimed as new here.

## Reproduce

Python 3.10 or later and its standard library suffice for the mathematical
builders and finite audits. From an extracted copy, run:

```sh
python3 reproduce.py
```

This rebuilds all new circuits and derived coefficient leaves, then runs
the independent checks. Its receipt is `certificates/REPRODUCTION.json`.
It does not execute the consistency-search machine, test whether an actual
ZFC refutation exists, or run a proof-assistant kernel.

Individual useful commands are:

```sh
python3 build.py
python3 materialize.py
python3 verify.py
python3 data/verify_channels.py
python3 data/check_toy_channels.py
python3 coefficients/audit_coefficients.py
python3 low_degree/verify.py
python3 quartic/build_verify.py
```

Several independent checkers explicitly reject `-O` and `-OO`; do not disable
their assertions. The native coefficient builder is
`coefficients/build_coefficients.py`; it can regenerate all four whole
integers from the supplied literal transition input. `REBUILD_CHECK.json`
records a separate reconstruction and comparison of all four raw hashes.

Compile the report from `report/`:

```sh
pdflatex -halt-on-error main.tex
pdflatex -halt-on-error main.tex
```

## Fixed coefficient bindings

The 9-, 10-, 12-, and 13-variable equations use the whole compact tuple in
`coefficients/COEFFICIENT_BINDING.json`, with native base `2^590069`.
The four ports occupy 295,388 raw bytes, or 9,445 compressed bytes. The
already shifted `MF_source` is used exactly once. The 14 nonliteral derived
coefficient leaves for the 9/10 circuits are fully materialized in `fixed/`
as signed magnitudes: 2,512,713 raw bytes, or 47,720 compressed bytes.

The quartic deliberately uses a separate whole package-34 tuple in
`quartic/upstream/34-integer14/coefficients/payloads/`, with native base
`2^1064921` and 532,479 raw payload bytes. Its parity contract is part of
its completeness proof. Do not mix ports between the two bindings.

Arithmetic operation counts charge every live binary addition, subtraction,
and multiplication, including multiplication by a numeral. Reuse is free;
fixed coefficients are leaves; every fixed power is expanded into binary
gates. These are arithmetic circuit counts, not bit-complexity or expanded
coefficient-height claims. The larger cancellation-resolved nine-variable
circuits are degree certificates, not the counted primary evaluators.

## Contents and proof boundary

| Location | Purpose |
|---|---|
| `report/` | Complete mathematical paper and compiled PDF |
| `generated/` | Main 9/10 DAGs, exact degree certificates and gate ledgers |
| `data/` | Raw parent, 94 source records, positions, symbolic source checker |
| `low_degree/` | Four small-degree DAGs, builders, proofs, independent checker |
| `quartic/` | Complete 45-integer quadratic system and exact quartic expansion |
| `coefficients/`, `fixed/` | Actual coefficient payloads, formulas and hashes |
| `proofs/` | New source proof, independent reviews, baseline audit |
| `upstream/` | Attributed inherited interfaces and calibration statements |
| `SOURCE_PINS.json`, `MANIFEST.sha256` | Provenance and distribution integrity |

The inherited ordinary compiler/calibration remains a named proof dependency;
this packet does not independently reconstruct its entire historical proof
chain. `proofs/LOGICAL_DEPENDENCY_REVIEW.md` and the copied `OBJECT_ZFC.md`
distinguish ordinary ZFC-formalizable mathematics from an external Lean iff
and from the still-unassembled object-language ZFC endpoint. Neither
consistency nor inconsistency is asserted. No global simplest equation is
known to follow from these improvements.
