# Exact examples

Each `*_certificate.json` is an algebraic observation and the full ordered word
that the independent matrix verifier replays. Run from the package root:

```sh
python -m boundary_kernel examples/separator_g3.json --genus 3
python -m boundary_kernel examples/separator_g3_certificate.json --verify
```

`separator_g3` is the standard `[a1,b1]` curve. Its central residue is 1 and,
under its explicit standard geometric realization, its complementary genera
are 1 and 2. `nonseparating_g3` is `a1`. `relator_g3` is the genus-three surface
relator and has zero signature.

`huge_conjugate_g3` represents
`u^(2^16384) [a1,b1] u^(-2^16384)`, where `u=a1 b2 b1 a2^-1`.
It has 18 SLP rules, 16,664 bytes in the benchmark's default compact JSON
serialization, and expanded length `8*2^16384+4`. The pretty-printed example
file has more bytes. Evaluation and certificate verification do not expand it.
Its free homotopy class is the same standard simple separator.

**`nonsimple_blind_g2` is an intentional negative example.** Its word is
`[[a1,b1], a1[a1,b1]a1^-1]`. It is nontrivial but has zero signature in every
class-two quotient. The certificate correctly says `UNDETECTED`; its
`simple_curve_consequence` field is explicitly conditional on an external
simplicity assertion that is false for this example. Do not interpret that
conditional field as a certified property of this word.

The three bank files use interleaved bit coordinates `(a1,b1,a2,b2,...)` and
identify characters with vectors by the symplectic form. The Lagrangian bank
and the non-Lagrangian genus-two triple are universal; the full standard
symplectic basis is not. `even_genus_transport_failure.json` records the
cache-invalidation counterexample and the nonzero extra data retained by the
safe quotient. These are algebra examples, not native knot-diagram fixtures.
