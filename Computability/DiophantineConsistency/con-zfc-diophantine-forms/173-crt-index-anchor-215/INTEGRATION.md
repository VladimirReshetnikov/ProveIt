# Suggested ProveIt integration

This archive is a self-contained research submission. It does not modify the
repository or reserve the next numbered submission directory.

Suggested descriptive directory name:

```text
Computability/DiophantineConsistency/con-zfc-diophantine-forms/<next>-crt-index-anchor
```

The submitted ZIP can also be retained under `docs/incoming/` following the
repository's current convention. Assign the number after checking the current
branch; the research baseline here is pinned independently.

## Suggested catalogue entry

**CRT index as semantic Pell anchor (215 variables).** Reuse the existing even,
cofinal CRT row-index representative to remove the derived-label range test.
A constructor-depth bound and a boundary-valid product-separation lemma retain
proof decoding at a larger weight parameter. The resulting 221-variable
arithmetic source reduces by exact integral projection and coordinate changes
to a quartic in 215 unrestricted integers: 154 squared quadratic residuals,
5,660 collected monomials, height 91,679. Complete coefficient data, 213/214
companions, ordinary proofs, selected inherited dependencies, independent
finite verifiers, and 26-stage byte-identical reconstruction are included.
The result is an ordinary ZFC-formalizable equivalence composed with the
identified C222/ZF/ZFC calibration; no new end-to-end Lean build is claimed.

## Baseline and attribution

All inherited comparisons use commit
`953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4`.

- Immediate arithmetic parent: `158-pooled-powers`.
- Factorial-free binomial CRT: `151-factorial-free-binomial-crt`.
- Affine CRT radix and sign/bootstrap proof: `157-linear-crt`.
- Quadratic and affine projections: `159-quadratic-projection-234`.
- Signed anchor, orientation and local budget: selected source135 notes.
- Original square-shell syntax and inherited C222 logical calibration:
  explicitly pinned in `PROVENANCE.json` and `inherited/SOURCE_BYTE_PINS.json`.

The supplied MIT No Attribution license matches the immediate parent and
repository. Retain the inherited notices and provenance even where the license
does not require attribution; they explain the mathematical dependencies.

## Checks before incorporation

Run the two verifier commands in README.md from the extracted directory.
`verification/NORMAL.json`, `OPTIMIZED.json`, and `PDF_QA.json` document the
release checks. A fresh extraction was also checked with the final manifest.
The release manifest intentionally excludes itself and transient TeX/Python
build products. Historical paths inside unchanged certificates are descriptive;
the release replay uses the portable paths in `OPTIMIZATION_CHAIN.json`.

The next useful proof-assistant task is formalization of the new
source-to-transcript equivalence, followed by a reproducible build composing it
with the inherited calibration. More bounded tests of Pell examples would not
close that formalization boundary.
