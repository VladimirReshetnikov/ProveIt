# Centered factorial consistency quartics

This portable subpackage replaces the two factorial graphs in the inherited
direct proof-calculus construction by a centered fixed-point identity.

## Delivered equations

All coefficients are fixed literal integers, and every polynomial is a sum
of squares of the supplied quadratic residuals.

| Directory | Domain | Variables | Residuals | Exact degree | Monomials | Coefficient height |
|---|---|---:|---:|---:|---:|---:|
| centered_output/natural_cap64 | Nonnegative integers | 395 | 313 | 4 | 8,292 | 83,843,425 |
| centered_output/natural_cap16 | Nonnegative integers | 398 | 316 | 4 | 6,948 | 211,184,624 |
| centered_output/integer_cap16 | Unrestricted integers | 853 | 453 | 4 | 9,747 | 2,445,790,974,704 |

The previous direct constructions have407 naturals or888 unrestricted
integers. The new equations save12 and35 variables, respectively. These are
improvements within the direct quartic branch. Other ProveIt branches have
fewer variables with different degrees or coefficient payloads.

## New mathematical mechanism

For all n,f in N,

    f=n! iff f=floor((2f+n+1)^n/(2^n*binom(f+n,n))).

For odd n=2h+1, the quotient simplifies to
(f+h+1)^n/binom(f+n,n). It is always at least n!, so a proposed fixed point
first forces f>=n!. A paired-factor product estimate then proves the
quotient is less than n!+1. The supplied proof also treats n=0 and n=1.

This removes both previous radius powers. It is composed with odd proof
padding, an odd majorant, and the shared radix B*(V_H+V_t+1). Both
numerators must appear in the radix to avoid a circular bound.

Read centered_factorial_proof.md for the unbounded argument. The inherited
source is the calibrated numerical proof calculus C222, not a simulation
of K215 and not Jones's universal polynomial. This subpackage supplies no
new Lean/Rocq proof object or object-language ZFC derivation. Its ordinary
proof is formalizable in ZFC; finite checks support the literal equations.

## Reproduce and verify

Python3.10 or later, standard library only:

    python3 centered_verify.py --receipt receipts/new-normal.json
    python3 -O centered_verify.py --receipt receipts/new-optimized.json

These commands independently check the actual arithmetic interfaces,
positivity and projection certificates and full coefficient expansions,
reject three corrupted certificates, and rebuild all defining artifacts
in an isolated temporary directory. They never search for a refutation or
a solution. To produce new coefficient files:

    python3 centered_factorial_build.py --output new-output
    python3 ConZFC_407_888_Quartics/code/integer_pipeline/build_integer.py --source new-output/equation.json --output new-output/integer_cap16 --max-support 16

The directory ConZFC_407_888_Quartics is an unchanged complete immediate
dependency. Its original LICENSE and NOTICE.md apply to its inherited
content, which includes the prior report and finite source/calibration
interfaces. PARENT_SHA256.json authenticates those copied files.
The new article is supplied by the containing research package; the
appendix files here print every R_i and S_i directly from the exact JSON.

## JSON convention

A residual term [c,[i,j,...]] means c times x_i*x_j*..., with repeated
indices denoting repeated factors. An empty index list is a constant.
Indices start at zero. The fully expanded single polynomial is also given
as a collected term list. The integer equation has no extra sign conditions:
the requisite guards are already among its residuals.

## Files

- centered_factorial_build.py: complete deterministic modified builder.
- centered_verify.py: independent arithmetic and equivalence audit, full replay.
- centered_factorial_proof.md: new proof and integration argument.
- centered_output/: literal equations, full expansions and exact certificates.
- render_centered.py: deterministic complete residual printer.
- appendix/: natural395_rows.tex and integer853_rows.tex.
- receipts/: verification outputs.
- ConZFC_407_888_Quartics/: preserved immediate dependency, sources and licenses.
- PARENT_SHA256.json and PROVENANCE.json: exact provenance.

