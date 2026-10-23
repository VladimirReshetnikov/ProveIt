# ProveIt integration notes

This is an additive research packet against
`4b4349064a750ba6347293b55874a7f92abdd0db`. It contains no edits to the
repository's existing Lean/Rocq projects and needs no network access for its
new Python builders or finite verifiers.

The primary catalogue candidates are:

- Twelve positive unknowns, degree 242 / 94 operations, and degree 258 / 89.
- Nine positive unknowns, degree 2,628,944 / 499; natural translation / 501.
- Ten unrestricted integers, degree 8,317,400 / 544.
- Forty-five unrestricted integers, quartic, 28 quadratic residuals.
- Thirteen positive unknowns, degree 132 / 83, as a companion tradeoff.

Preserve the distinction between positive, nonnegative, and unrestricted
integer domains. Preserve the distinction between scalar equations and a
quadratic residual system. The twelve-positive degree-314 / 91 construction
is an explanatory intermediate, dominated by the degree-258 / 89 form.

The release contains the whole compact 39/44 coefficient tuple for the
small-variable equations and the whole package-34 tuple for the quartic.
These are separate coherent instances. Their ordinary compiler theorems,
including parity and population contracts, remain inherited dependencies.

`SOURCE_PINS.json`, nested source pins, `MANIFEST.sha256`, and the archive
receipt identify the distributed inputs. Run `python3 reproduce.py` in an
extracted directory to audit the new outputs. Reproduction establishes
the finite circuit/certificate facts described in the report; it does not
automatically formalize the new theorems.

Suggested review order: the compact report's Section 3 (separate norms and
Pell quotient), Section 4 (degree channels and unconditional carrier),
Section 5 (nine-variable margin), Section 6 (Sun source contract), and
Section 7 (quartic guard reconstruction). Section 8 and
`proofs/LOGICAL_DEPENDENCY_REVIEW.md` give the exact ordinary-mathematics
versus object-language formalization boundary.
