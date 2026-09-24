# Removing the redundant gap from E13

The 129-operation baseline requires positive integer witnesses satisfying

\[
c=2r+1+\kappa+\varphi_{\rm old}.
\]

Replace this equation by

\[
c=\kappa+\varphi_{\rm new},\qquad \varphi_{\rm new}>0.
\]

Keep every other equation and every other witness domain unchanged. In
particular, E15 and E19 require

\[
d^2-(a^2-1)c^2=1,
\qquad
\mu^2-(a^2-1)\kappa^2=1,
\]

with positive integers \(a,c,d,\kappa,\mu\). The modified positive-integer
system is equivalent to the baseline by an explicit change of the slack
witness. No numerical experimentation is used to justify this change.

## Elementary Pell spacing lemma

Let \(a\ge2\), set \(D=a^2-1\), and suppose

\[
d^2-Dc^2=\mu^2-D\kappa^2=1,
\qquad c>\kappa>0,
\]

where \(c,d,\kappa,\mu\) are positive integers. Then

\[
c-\kappa\ge2a-1.
\]

Indeed, \(d/c=\sqrt{D+1/c^2}<\sqrt{D+1/\kappa^2}=\mu/\kappa\), so
the integer \(t=\mu c-d\kappa\) is positive. Also
\(v=d\mu-Dc\kappa>0\), since both \(d>\sqrt D\,c\) and
\(\mu>\sqrt D\,\kappa\). Multiplication of the two unit-norm expressions
gives the exact identities

\[
v^2-Dt^2=1,
\qquad c=\mu t+\kappa v.
\]

As \(t\ge1\), we have \(v^2=Dt^2+1\ge D+1=a^2\), hence \(v\ge a\).
Likewise \(\mu\ge a\). Therefore

\[
c-\kappa=\mu t+\kappa(v-1)
\ge a+\kappa(a-1)\ge2a-1.
\]

## Applying the lemma

E1 and the positivity of \(x,y,e,\ell,g,\alpha,q\) imply
\(b>xy\ge1\), so \(b\ge2\). E2 gives
\(q^4=1+\lambda(b^5-1)\ge b^5\), whence \(q\ge2\). E6 gives
\(n=q^{16}\ge2\). E12 and \(w,s\ge1\) consequently imply

\[
a=(wn^2+1)rsn^2\ge(4+1)r\cdot4=20r.
\]

Thus \(a\ge2\), and \(2a-1\ge40r-1>2r+1\), since \(r\ge1\).
In the new system, \(c>\kappa\). The spacing lemma now gives

\[
\varphi_{\rm new}=c-\kappa\ge2a-1>2r+1.
\]

Hence
\(\varphi_{\rm old}=\varphi_{\rm new}-(2r+1)\) is a positive integer and
restores the original E13. In the reverse direction,
\(\varphi_{\rm new}=\varphi_{\rm old}+(2r+1)>0\) immediately gives the new
equation. The other witness values remain the same in both directions.

The symbolic verifier checks both residual substitution identities. The
argument above supplies their positive-domain justification.

## Operation count

The baseline already computes \(2r+1\) for E17. Its E13 then needs two
further additions, \((2r+1)+\kappa\) and addition of \(\varphi_{\rm old}\).
The new E13 needs only \(\kappa+\varphi_{\rm new}\), saving one addition.
