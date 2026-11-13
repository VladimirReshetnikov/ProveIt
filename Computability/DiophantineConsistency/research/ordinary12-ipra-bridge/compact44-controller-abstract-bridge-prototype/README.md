# Symbolic compact44 controller unit in models of IΣ₁

`CompactActualUnitTransport.actual_unit` proves, in any model of IΣ₁, that
the compact controller expression `Gamma` is a unit modulo
`590069 * 581197^(m+1)` for every model `m,e`, taking
`K = paramKernel rho`, `rho = 2^67`, `N = 581197^(m+1)` and
`w = 581197^e`. The exact expression is defined by
`ArithmeticConstructionUnitCompact44.Gamma`. There is no remaining K-residue
hypothesis in this theorem. The exponents and inverse can be nonstandard
model elements.

The four compiled clients keep the conversion steps separate:

1. `AliasResidueNumeral` transports the checked alias residue from the
   abbreviation `Modulus` to the exact numeral.
2. `AliasUnitGivenResidue` specializes the conditional unit theorem to the
   alias, retaining that explicit residue hypothesis.
3. `AliasUnitDischarged` supplies the numeral-form residue.
4. `ActualUnitTransport` uses the already checked `kernelAlias_eq` to return
   to the actual symbolic `paramKernel rho`, by explicit equality transport.

All four bounded author-side compiler stages exited 0 without warnings;
their printed axiom reports contain `propext`, `Classical.choice`, and
`Quot.sound`, and no `sorryAx`. Exact source and log hashes, commands,
dependency listings, output-object hashes and terminal results are retained
in `observations/terminal.json` and the companion logs. Each checked source is
byte-for-byte its successful input; its original opening comment calling it
uncompiled is historical. The runner checks the prior same-side build's four
direct object hashes and the separately compiled alias object before starting.

The earlier direct join and named-alias client failures are preserved in the
companion [join](../compact44-symbolic-controller-join-prototype/README.md)
and [alias](../compact44-symbolic-controller-alias-prototype/README.md)
records. This result is an incremental single-author build over the shared
symbolic provider, not a paired replay or a fresh authenticated project or
package closure. The earlier controller-data rebuild emitted the documented
unused-section-variable linter warning. Inherited transitive and dynamic
provider ancestry, and between-check mutations, are not excluded.

This theorem establishes only a model-level unit for the symbolic factor. It
does not identify the retained file bytes or displayed coefficient, prove
that `Gamma` is the variation of the packed rank, construct safe dummy
locations or a positive graph zero, or produce an iPRA derivation.
