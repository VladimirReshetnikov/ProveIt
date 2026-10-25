# Second-order Lucas correction at the scale Y = q s

The principal artifact is `equation_bV.json`: a single fixed integer
polynomial in ten strictly positive integer variables, with exact degree
304, evaluated in 87 binary arithmetic operations (53 multiplications,
18 additions, 16 subtractions). Squares and multiplication by constants
are counted. The 86-operation, degree-410 `equation_V2.json` is a dominated
control retained to separate the index correction from the sharper
transport estimate.

The new argument replaces the old first-index error by its second-order
Lucas correction. It first upgrades a q^3 index congruence to the q^4
modulus needed by the rank bound; after recovering the exact index, it
recovers the whole q^6 denominator and the missing q^2 divisibility of s.
The proof handles arbitrary prime divisors of q, including 2 and 3, and
all negative preliminary ranks before source positivity has been proved.

## Mathematical scope

`PROOF.md` gives the ordinary unbounded proof. `section.tex` supplies the
same result as a section for the enclosing report; it intentionally has
no document preamble or independent PDF. The polynomial's absence of a
strictly positive integer zero is ZFC-provably equivalent to syntactic
Con(ZFC), after composition with the explicitly identified inherited
native/refutation calibration.

This is an arithmetic improvement within that calibrated route. The
module does not prove consistency, claim a global minimum, certify
literature-wide novelty, or supply a new end-to-end proof-assistant object.
Its `parent/proof_sources/` directory retains inherited arithmetic proofs
and interfaces needed for the new argument. It is not a bundle of every
transitive native-calibration proof and is not a standalone Lean build.
The four coherent fixed coefficients and their actual bytes are retained;
they are not additional variables or free parameters.

## Reproduction

Run these commands from this directory with Python 3:

```sh
python3 build.py --check
python3 verify.py --receipt CHECK.json
python3 -O verify.py --receipt CHECK_OPTIMIZED.json
python3 parent/rebuild_coefficients.py
```

The generator reads only the frozen parent JSON graphs and reconstructs
the two supplied graphs byte for byte. It imports no upstream executable.
The independent verifier does not import the generator. It reuses only
the credited parent's sparse-polynomial arithmetic implementation, and
specifies its expected new formulas separately. The checker verifies all
actual rows via 37 free-polynomial cuts per graph, recounts the live
arithmetic operations, authenticates the compressed and raw coefficient
bytes, and propagates the entire top homogeneous polynomial to certify
the exact degrees. It rejects both alternative arithmetic operators at
every actual row and an omitted-correction corruption.

The separate coefficient script reconstructs all four numerals from the
printed finite BFS943 recipe and checks equality against the stored
payloads. The Taylor identities are checked exactly. The 540 recurrence
controls and 2,816 corrected-index controls are finite diagnostics; they
do not replace the unbounded proof. `CHECK.json` and
`CHECK_OPTIMIZED.json` retain the exact finite receipts.

## Source and attribution

The parent comes from the compact component of
`docs/incoming/ConZFC_Centered_Residues_2026-10-25.zip` at ProveIt commit
`3ecd6a6cf53d47519228328567f45fb7ee9781d9`. The earlier failed q-linear
direction is described in the same snapshot's
`ConZFC_Residual_Bases_Denominator_Engineering_2026-10-25.zip`, Section 8
of its compact proof. The fractional positive carrier is also informed
by the q-squared predecessor in
`ConZFC_Coprime_Products_and_Positive_Centers_2026-10-25.zip`.

All retained upstream licenses and attribution notices are under
`parent/licenses/`. The copied source-file hashes and repository origins
are recorded in `parent/proof_sources/parent_source_pins.json` and the
retained parent ledger. `PROVENANCE.json` identifies this module's new
files and the exact parent component. The new analysis and artifacts
were prepared with AI assistance. A separate mathematical review within
that workflow is distinct from outside human peer review.
