# Independent review: P73 conditional auxiliary sphere

The external same-zero argument and 91-operation graph pass review. For positive inputs, `a>0`, `Delta≥8`, `I>0`, and `u=y−V>0`. If `f≥2`, then `Q=Delta*(f²−1)>1`. If `Fa=0`, neither V nor y can vanish alone, and `Q*V²=(Q−1)*y²`. Since Q and Q−1 are coprime, prime valuations force each to be a square; consecutive positive squares are impossible. If instead `f=1` and `Fa=0`, the strong residual is `−Delta*I²`, whose magnitude is at least 8. Consequently `Fa²+As²−1≥0` on all positive inputs.

Modulo 4, Delta and `f²−1` are each 0 or 3, so Q is 0 or 1 and Fa is congruent to a square. Thus Fa is never −1. At a zero of the new output, nonnegativity forces A0=A1=0 and `Fa²+As²=1`; the Fa=0 branch is excluded, leaving Fa=1 and As=0. This is exactly the parent zero condition, and the converse follows directly. Both directions hold at the same positive valuation.

The complete graph delta and all 91 live gates and inputs were checked. The exact tail identity is `Pnew=Pold+2*(Fa−1)`. The independently reviewed parent degree bound is 30 and the factored gap bounds Fa by 13; hence the new degree is at most 30. A separate weighted affine ray through the authenticated actual little-endian ports has nonzero degree-30 coefficient 284041780 modulo 1,000,000,007, establishing exact degree 30. The author receipt reproduces byte for byte.

The proposed counterexample was independently evaluated at actual ports: all coordinates except u are 1, `u=R>0`, `Fa=0`, `As=−1215`. The graph's R is independent of u, and its independently computed 2,360,284-bit value matches the recorded hash. This refutes unconditional nonvanishing of Fa; it does not assert a full equation zero.

This is a source-only result with no operation saving, new Lean theorem, independently rebuilt foundational ancestry, or JSON/PDF binding. P72 physical port payloads match the pinned P61 hashes; P61's own payload paths were absent in the earlier review. Run `python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary13-p73-conditional-sphere91-independent/check.py` from the repository root.
