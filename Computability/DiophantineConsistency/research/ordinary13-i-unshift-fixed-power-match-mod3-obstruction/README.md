# Fixed-port obstruction to one exact power-matching route

For the exact compact coefficient tuple and **J = 1**, the necessary congruence

\[
  4L^2+2L-1\equiv MC+q\,MF\pmod{q^2-1},\qquad q=1+\beta,
\]
has no integer solution. This blocks the particular construction with
\(n=L(2L+1)\) and actual rank \(R=2n-1\), including the large-\(L\) choices
needed by the coarse-bounds witness. It does **not** show that the i-unshifted
graph has no zero at the fixed ports, or that any two graph zero sets differ
in existence; other values of J, shifted rank relations, and other witness
constructions remain open.

## Proof

The pinned fixed recipes give \(\rho=2^{67}\), \(\beta=\rho^{8807}-1\),
\(MC=\mathrm{lowNat}\), and \(MF=\beta+\mathrm{highNat}\). Modulo 3,
\(\rho=-1\), \(\beta=1\), and \(q=2\), so \(3\mid q^2-1\).
The low-mask support has 492 even and 493 odd indices. The pinned
`concrete_recipe` therefore yields

\[
 MC\equiv1-(492-493)-2(-1)^{1063}\equiv1\pmod3.
\]
The high-mask digits, read least-significant first from the pinned source,
have weighted sum \(\sum_j d_j(-1)^j\equiv0\pmod3\). Hence
\(\mathrm{highNat}\equiv0\), \(MF\equiv1\), and
\(MC+qMF\equiv1+2\equiv0\pmod3\). The actual graph rows give
\(R=G(q^2-1)+J(MC+qMF)\), so in the selected J=1 slice its actual rank
is divisible by 3, independently of the other graph coordinates.

But for \(L\equiv0,1,2\pmod3\), the proposed matching value
\(4L^2+2L-1\) is respectively \(2,2,1\pmod3\). None equals 0. The
claimed modulus \(q^2-1\) is itself divisible by 3, making the congruence
impossible.

The Python certificate pins the concrete recipes, `Nat.ofDigits` digit
convention, and literal graph. It checks the support and high-digit recipes,
computes the high residue both by Horner evaluation and by the explicit
weighted sum, computes the low residue both from the support formula and from
the digits, and enumerates all three residues for L. Its output is reproduced
with:

```sh
python3 -I -S -B research/ordinary13-i-unshift-fixed-power-match-mod3-obstruction/check.py
```

This is a standard-integer modular proof and source audit. It does not run Lean,
prove an internal iPRA result, or materialize the huge compact coefficients.
The predecessor's coarse-bounds construction uses different positive ports;
this obstruction does not invalidate that non-fixed-port example.
