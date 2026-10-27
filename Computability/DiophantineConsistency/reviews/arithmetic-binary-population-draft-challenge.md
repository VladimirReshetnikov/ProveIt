# Binary population draft: scoped source challenge

27 October 2026. Full source-only read of ROOT's uncompiled 224-line main
and 40-line Checks: no mathematical or public-interface finding.

- Main SHA: `dae4cc6d1946b1b6e0650572dc5a11451be30d9ffb519d1b342473de9ac59671`.
- Checks SHA: `b1e882c8d79b3070d5a3ae638b0f11b412f8bc8af7f0517d3e648b036456bc38`.

The fixed PR blueprint orders successor arguments output/previous/index/a;
the result graph orders output/n/a. Population's explicit length/prefix
composition is Sigma1, and its graphDelta instance follows actual unique
totality. Instances precede the genuine internal successor inductions.
There is no externally finite sum or standardness premise.

The prefix shift induction covers a=0; the even population proof correctly
separates a=0 before invoking positive even length. Concatenation fixes A
and generalizes only bounded b. The quotient bound follows from
2*(b/2)≤b<2*exp(n), and both populations use the same remainder.

In the complement proof, q<E gives q+1≤E and s=E−(q+1), hence s+q+1=E.
Together with r≤1, the exact additive identity
`(2*s+(1-r))+(a+1)=exp(n+1)` proves the intended truncated complement.
The argument does not assume the sign of an unproved difference. Its
remaining cancellation invokes the same bounded induction hypothesis;
zero width and both low-bit cases are covered. Prefix stabilization and
population bounds use the actual zero-above-length fbit API.

This challenge includes the complete current proof text and Checks, plus
the PRF, binary-bit/length and definability contracts listed in the separate
plan peer review. It does not assert successful elaboration, axiom audits,
object provenance or independent replay of a new leaf. The plan inventory
was independently authenticated separately; eventual compiled source and
proof objects still require their own frozen review.
