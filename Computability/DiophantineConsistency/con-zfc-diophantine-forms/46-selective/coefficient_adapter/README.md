# Smaller native coefficients: complemented receivers and a shared parity anchor

This is a separate, complete ordinary mathematical adapter for the inherited
K215 native/Pell compiler. The main ten-integer and nine-positive-variable
polynomials in this release **retain their source31 coefficient tuple**.
No coefficient port from this directory is silently substituted into them.

## Improvement over the latest complete source44 tuple

| Metric | Source44 | This adapter |
|---|---:|---:|
| Radix | 2^67 | 2^89 |
| Native cell length | 8,807 | 4,831 |
| Base | 2^590069 | **2^429959** |
| Unary selector modes | 943 | 457 |
| Native supported positions | 986 | 520 |
| Four raw coefficient payloads | 295,388 bytes | **215,492 bytes** |
| Largest coefficient | 592,884 bits | **434,054 bits** |
| Delivered deterministic gzip payloads | See source44 | 4,751 bytes |

The base exponent decreases by 27.1341%; raw coefficient storage decreases
by 27.0478%. The larger radix buys a shorter native cell and a smaller
complete base. This changes the fixed coefficient heights, not the number
of unknowns or arithmetic operations of a compatible arithmetic skeleton.

The four port bit lengths are 429959, 434054, 429959, and 429960, in the
order beta, K, MC, MF_source. The fourth port is the **shifted** high
mask. Every use must replace all four ports coherently and, for Jones or
Sun compression, rebuild the derived index constants.

## New mathematical mechanism

Source40 supplied a 457-selector receiver factorization but explicitly
left an empty-cell soundness obligation open. Source44 supplied aggregate
complement clauses. This adapter combines them with complemented, doubled
horizontal labels and reuses the copied west parity bit as both the shared
current anchor and one summand of the aggregate anchor count.

The resulting congruence forces that copied bit to equal the selector
count. With no selected tile, only two standalone anchors remain available;
an interval bound then forces every payload, copy, and anchor to zero.
With a selected tile, the same congruence forces the exact complemented
edge labels and both anchors to one. Thus the old empty-cell gap is
resolved, including all receiver payload assignments.

SEPARATED_PROOF.md contains the complete universal local proof,
synchronization, exact fixed coefficient recipe, carry and population
bounds, controller certificates, and completeness argument.
paper_section.tex gives the shorter article appendix.

## Reproduce from the release root

Python 3 and its standard library are sufficient:

    python3 coefficient_adapter/build_separated.py
    python3 coefficient_adapter/audit_separated.py
    python3 -O coefficient_adapter/build_separated.py
    python3 -O coefficient_adapter/audit_separated.py

The scripts also work when invoked by absolute path from another working
directory. They resolve their inputs relative to their own location.

The generator binds the fixed parameters b=89, L=4831, and
lambda=106261; it does not run K215 or wait for a refutation.
The independent auditor imports neither builder and uses checks that
remain active under python -O. It reconstructs the literal language,
all coefficients, and their actual bytes.

The independent audit reports:

- 1,479 occupied expansions and 536 impossible extra receivers;
- 65,076 physical single-bit corruption checks;
- all 131,072 empty auxiliary assignments, with only the zero payload
  physically realizable;
- 37,960 complete native basis identities;
- exact mask populations, carry bounds, prime/order/lifting and controller
  units, and byte-for-byte reconstruction of all four coefficient files.

These are finite certificates of the stated finite facts. The universal
proof is in SEPARATED_PROOF.md; no bounded simulation is treated as a
proof of ZFC consistency or machine nonhalting.

## Dependencies, provenance and scope

The proof is ordinary mathematics formalizable in ZFC, composed with the
explicitly inherited native/Pell compiler, marked Wang-language theorem,
and K215/refutation calibration. This is not a new end-to-end Lean/Rocq
certificate or an exported object-language ZFC derivation.

SOURCES.json pins every retained inherited source to repository commit
124c07c0b77a9e20e84676514d8b1ff78536ea3f. All listed inherited files were
verified byte-identical to their pinned Git blobs. Source36 supplies the
literal K215 data; source40 supplies the factorized receiver construction,
gates and starting geometry; source44 supplies the complement principle
and controller interface. Their original notices and licenses remain
under their original filenames and licenses/.

build_factorized.py is an unchanged inherited helper used for its finite
mode language and arithmetic routines. Its historical experimental status
applies to its old decoder. The new decoder, shared anchor and complete
tuple are defined in build_separated.py and proved independently here.
