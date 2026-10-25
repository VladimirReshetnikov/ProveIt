# Attribution, provenance, and verification scope

Prepared for Vladimir Reshetnikov and the ProveIt project on 25 October
2026, with AI assistance. The comparison snapshot is
`3ecd6a6cf53d47519228328567f45fb7ee9781d9` of
<https://github.com/VladimirReshetnikov/ProveIt>.

`SOURCE_LEDGER.json` records the exact original incoming ZIP hashes,
retained source paths, proof dependencies, raw and final polynomial hashes,
and the historical coordinate-name transfer. Repository placement of an
earlier contribution is not itself evidence that its mathematical claims
have been independently accepted.

## What is new in this contribution

The new mathematical step recovers the exact factorial digit and its
positive sign before using the ceiling remainder and slack inequalities.
The cofinal restriction `q=(6z+3)^2` gives a nonunit positive radix. A
retained common-denominator ratio then forces an early exponent bound;
the full binomial coefficient sum bounds the factorial digit and its low
remainder. Exact congruence recovers the positive digit. This permits two
separate ceiling sign graphs to be replaced by one weak product graph
`r*s=a^2+b^2+c(c+1)`.

The proof is in `proofs/NEW_ARGUMENT.md` and the research article. The
resulting source is explicitly compiled, and the final 247-variable
quartic includes a frozen coefficient-reduction sequence and separate
finite algebra verification. The four residual-row operations used for
that final coefficient reduction are supplied in full.

These claims concern the inspected source lineage and the stated metrics.
They do not assert literature-wide priority, a globally simplest equation,
a proof of consistency, or a decision of whether the equation has a zero.

## Inherited mathematical and computational contributions

**Common normalized remainders.** The main predecessor is the direct
component of `ConZFC_Common_Remainders_Radix47_2026-10-25.zip`. Its
252-variable construction, normalized low-remainder norm, three ratio
equations, and ordinary proof closure are retained under
`source/inherited_common/`. The numerical C222 proof calculus, arithmetic
and CRT compilation, factorial fixed point, signed Pell frame, semantic
anchor, strict amplification budget, Horn factoring, integral monic
projection, and centering machinery are inherited through that component.
The C222/ZF/ZFC refutation calibration remains explicitly inherited.

**Pell comparison center and orientation.** The deterministic comparison
center `D=A+(1-A)H^2`, its weaker modulus C, and its exceptional-anchor
proof come from `ConZFC_Symmetric_Remainders_2026-10-25.zip`. The exact
retained proof is `proofs/PELL_CENTER_PRIOR.md`. This packet uses the
**full fourteen-pair linear orientation pool**: all fourteen principal
abscissas are canonically oriented before arithmetic-front signs are
recovered. It does **not** use the prior archive's further selective-nine
orientation optimization. The linear full-pool argument is a reused
ingredient, not the new sign-recovery theorem.

**Odd-square cofinal witnesses.** The odd-square radix and parity-selective
CRT predecessor is credited to
`ConZFC_Symmetric_Residue_Budgets_2026-10-25.zip`. Its proof is retained
as `proofs/ODD_SQUARE_PRIOR.md`. The restriction to an odd square with
square root divisible by three, and its use before recovering the
factorial digit's sign, are explained separately in the new proof.

**Coordinate shears.** All 76 ordered integral coordinate shears are
reused from `ConZFC_Shared_Residue_Bounds_2026-10-25.zip`. Their source
equation and shear list are preserved in `certificates/`. Every step is
transferred by exact historical coordinate name, not by assuming the
old indices still agree. `certificates/shear_transfer_provenance.json`
records the complete mapping. The new and old equations are distinct;
transferring the recipe does not imply identical coefficient effects.

**Residual bases.** The earlier
`ConZFC_Residual_Bases_Denominator_Engineering_2026-10-25.zip` is credited
for its residual-basis and denominator-engineering work and is included
in the source comparison ledger. Invertible integral residual-row
operations are inherited methodology. This archive's files are not
needed by the included replay scripts; the four actual operations for
the present equation are printed in their own certificate.

Standard number-theoretic ingredients, including Pell recurrences,
binomial identities, the Chinese remainder theorem, and the ternary
representation of nonnegative integers, are not claimed as new discoveries.

## Licensing

New material follows the repository's **MIT No Attribution license
(SPDX: MIT-0)**, supplied in `LICENSE`. Retained material keeps its
existing notices and license files. The copies of `LICENSE` at the root,
in `source/inherited_common/`, and in its retained round-17 source
component are byte-identical MIT-0 texts. This notice adds attribution
and explains provenance; it does not impose an additional license term
or replace the original license.

## Meaning of verification and review

The ordinary mathematical argument is formalizable in ZFC and is
composed with the named inherited refutation equivalences. The finite
Python verifiers check literal source deltas, exact polynomial identities,
integral coordinate and residual maps, coefficient collection, and the
printed formula. They do not prove unbounded number-theoretic statements
by sampling and do not decide consistency.

The preserved Lean files identify formal interfaces and source ancestry.
This packet does not claim a newly compiled end-to-end Lean/Rocq proof or
an emitted object-language ZFC derivation. Its retained common component
is self-contained for its standard Python verification: all 50 pinned
source/proof files are present with the expected hashes, and its standard
verification completed successfully. That finite closure is distinct
from a complete proof-assistant import closure.

Independent reviews here mean separate mathematical and implementation
work within this AI-assisted workflow. No outside human refereeing,
institutional endorsement, or external validation is implied. Existing
repository files, branches, issues, and pull requests were not modified
by preparation of this research package.
