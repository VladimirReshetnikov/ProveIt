# Independent review: universal zero after unshifting s

The [reviewed 60-operation candidate](../../research/ordinary10-divisible61-s-unshift60-universal-zero/README.md)
is obtained from the literal 61-operation graph by deleting exactly
`s=n_s+1` and replacing the s input in the Y row by `n_s`. Its stated
natural zero exists for every natural port tuple with beta≥2, including the
fixed symbolic compact tuple. This is a pointwise obstruction to using the
old positive-s shift to justify that deletion; it does not prove the 61- and
60-operation equations have different existential zero status or establish
an iPRA/Con(ZFC) equivalence.

For arbitrary beta≥2 and natural K0, let
\(L=\lceil(K_0+2)/\beta\rceil\) and
\(w=\beta L-K_0-1\). The ceiling inequalities give
\(0\le\beta L-(K_0+2)<\beta\), hence \(L\ge1\) and
\(1\le w\le\beta\). Thus
\(h=(\beta-1)(w+L)-1\ge1\). With q=beta+1, set

\[
R=(1+\beta^2)(q^2-1)+MC+qMF.
\]

All mask terms are nonnegative, so R≥1. The stated input tuple
\((1,0,0,w,0,h,1,1,R-1,0)\) is therefore natural. The changed graph has
\(Y=U=\ell=0\), \(C=\beta-1\), \(k_{base}=R\), and
\(k=R+1\). Its exact carrier satisfies

\[
C(X+K_0)-F=\beta\big((\beta-1)(w+L)-1\big)=\beta h.
\]

The first normalized residual is zero at tau=1, and the actual main root
and residual vanish because U=0 and \(R-k_{base}=0\). Thus every squared
residual and the literal output are zero. At the **same input tuple**, the
old graph instead has positive Y, X and k; its first normalized residual is
\(-\ell(\ell+k)<0\), so its sum-of-squares output is positive. This
last fact remains pointwise; a different old-graph witness is not excluded.

The independently pinned compact source defines
\(\beta=2^{67\cdot8807}-1\ge2\) and its ports are natural-number
expressions, so the proof includes that tuple without expansion.

The checker independently verifies the exact row edit, topology and all 60
live operations. It evaluates every candidate row over the sparse integer
polynomial ring in beta,w,L,MC,MF with \(K_0=\beta L-w-1\), and confirms
the three residuals and output vanish identically. Bounded ceiling controls
include a large input; the general ceiling argument above establishes
naturalness. The author receipt reproduces. No Lean, build, staging, model
provider, or endpoint proof was performed.

```sh
python3 -I -S -B reviews/ordinary10-divisible61-s-unshift60-universal-zero-independent/check.py | cmp - reviews/ordinary10-divisible61-s-unshift60-universal-zero-independent/receipt.json
```
