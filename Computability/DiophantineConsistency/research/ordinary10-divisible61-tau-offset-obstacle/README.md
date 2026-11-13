# The direct tau-offset rewrite does not save a gate

For the literal [10-variable, 61-operation two-norm graph](../ordinary10-two-norm-divisible61/README.md),
one natural reparameterization of the normalized first root is
\(t=\tau-\ell\). At a zero its first equation is
\(\tau^2=1+\ell(\ell+k)\); because all ports and inputs are natural,
\(\ell\ge0\), \(k\ge1\), and hence \(\tau>\ell\). Thus t is a
positive natural number. Conversely any natural t satisfying the transformed
first equation gives a valid original tau by \(\tau=\ell+t\); the other
residuals do not use tau. These are exact two-way **zero-witness** maps,
not a claim of a new graph or original-parent equivalence.

The normalized first residual under this change is the exact identity

\[
(\ell+t)^2-1-\ell(\ell+k)
=t^2-1+\ell(2t-k).
\]

The existing literal computation of this residual uses five binary operations
once ell and k are available: ell+k, its product with ell, addition of 1,
tau², and subtraction. The displayed offset expression uses six in the
direct evaluation: t², subtract 1, twice t, subtract k, multiply by ell, and
add. Thus this straightforward cancellation **adds** one local gate. Another
circuit with global sharing or another zero map is not excluded; this is not
a gate lower bound.

Under the candidate's beta>0 and K0>0 assumptions, its reviewed main-norm
arguments additionally force \(X>0\), \(q\ge2\), and \(k>q\). Hence
\(\ell=XY^2k>0\), and both exact square differences are positive:

\[
\tau^2-(\ell+1)^2=\ell(k-2)>0,\qquad
(\ell+k-1)^2-\tau^2=(k-2)(\ell+k)>0.
\]

Consequently \(2\le t\le k-2\). In particular neither simple endpoint
substitution \(\tau=\ell+1\) nor \(\tau=\ell+k-1\) can describe a
zero under those port hypotheses. The result does not exclude other
coordinate changes or prove a lower bound on equation size.

The checker pins the literal graph, reviewed norm bounds and prior independent
review; confirms tau occurs only in its squared first-root row; verifies the
offset and square-difference identities in an exact integer-polynomial ring;
and checks bounded controls. It counts only the displayed local expressions;
it does not assert global optimality. No Lean, build, staging, model proof or
parent bridge is produced.

```sh
python3 -I -S -B research/ordinary10-divisible61-tau-offset-obstacle/check.py | cmp - research/ordinary10-divisible61-tau-offset-obstacle/receipt.json
```
