# Independent external review

Under the reviewed Pell-floor and P72 hypotheses, `q=2^t`, `q³|Y=sq³` and the floor valuation give `popcount(R)=3t+v2(s)+2`. The exact port payloads verify the stated mask populations, low bits, strict mask sum, and residues. Since `beta=2^B−1` divides `q−1`, B divides t; repeating both B-bit masks h=t/B times proves `popcount(A)+popcount(Z)=t` and the same low-bit conditions. They imply `popcount(G0)=t+2` and `A+Z>q−1`.

The rank identity is `R=(G+1)(q²−1)+G0`. If positive admissible `G<G0`, split it as two base-q² blocks `G+1` and `G0−G−1`; their sum is G0, so the number of binary carries is at most `2t−1` and `popcount(R)<=3t+1`, contradicting the lower bound. If `G>=G0`, the rank blocks are `G` and `q²−1−(G−G0)`, so `popcount(R)<=3t+2`. Equality follows, giving `v2(s)=0` and no carry in `G0+(G−G0)`.

Writing `G=q*h0+ell`, no carries gives `h0>=Z−1` and `ell>=A+1`, hence `h0+ell>q−1`. The earlier candidate bound gives `h0<=q−2`; Euclidean division by `q−1` then uniquely gives `u=h0+1`, `r=h0+ell−(q−1)` with `2<=u<=q−1`, `1<=r<u`. Thus positive old scalars exist for the same gap, q, and R. This is not yet an old zero: equality of the gaps implies `C=C0+q*d0`, and the reviewed repair criterion leaves `(q−1)|d0*(K+w+1)` as an exact additional requirement. Its z-positivity is automatic from the established lower rank and `w=2^(R−t)>=q`.

The conditional 11-divisor claim also checks: for `20|t`, the actual port residues give q=6 and J=5 modulo 10; odd R forces R=5 modulo 10. Then 11 divides q−1 and `w=2^(R−t)=-1 mod 11`, while K=0 mod 11. This only rules out a blanket coprimality argument on that exponent branch; no candidate zero on it is asserted.

The checker verifies compressed/raw port hashes and actual repeated-mask facts, independently checks bounded masks, no-carry/gap reconstruction, transport algebra and residues, reproduces the author receipt, and reruns the Pell-floor and scalar-repair audits. Finite cases are controls, not a replacement for the carry proof. Existing P72/source ancestry qualifications apply. No new Lean proof, full reverse equivalence, or R<26 conclusion is claimed.
