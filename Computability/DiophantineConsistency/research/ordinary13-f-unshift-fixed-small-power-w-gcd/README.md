# Fixed compact F-unshift: first-carrier restriction for eight w classes

For the actual fixed compact tuple in standard integers, suppose the literal
F-unshift graph has \(J=1\), \(F=0\), \(C=q-\alpha>0\), and a zero
first residual. If

\[
w\equiv2^e\pmod\beta\quad\text{for any }e\in\{0,1,\ldots,7\},
\]
then \(C=\beta\) and \(\alpha=1\). In particular this holds for w=1.
The conclusion applies to each of the eight entire congruence classes, not
just eight small values. It neither rules out this slice nor constructs a full
graph zero; other w classes and other J values remain open.

The [preceding norm analysis](../ordinary13-f-unshift-fixed-positive-gap-norm-congruences/README.md)
shows directly from the signed first root that
\(\beta\mid C(w+K_0)\). Here
\(q=\beta+1=2^{590069}\), \(\alpha\ge1\), and \(C>0\), giving
\(1\le C\le\beta\). The exact fixed kernel has

\[
K_0=\beta\rho^{42}+K',\qquad \rho=2^{67},
\]
where the pinned symbolic source specifies K′ through its 943 ordered rows
and 41 selector positions. Direct exact integer computation from those
source recipes gives

\[
\gcd(\beta,K'+2^e)=1\quad(0\le e\le7).
\]
Because \(w+K_0\equiv2^e+K'\pmod\beta\), the first-carrier divisibility
then implies \(\beta\mid C\). The displayed bound forces \(C=\beta\),
and \(\alpha=q-C=1\). This uses the first residual only; full-output factor
extraction is unnecessary for the conditional statement.

The checker pins the literal first-norm analysis, fixed beta, source-defined
kernel, selector recipe, all 943 rows and the 41 slots. It reconstructs K′
with exact bit shifts and recomputes each gcd. The largest beta has 590,069
bits (about 74 kB) in memory; no giant numerals or intermediate values are
printed or written to disk. No Pell iterates, Lean process, build, model
provider, or endpoint proof is involved. Reproduce from
`Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-f-unshift-fixed-small-power-w-gcd/check.py | cmp - research/ordinary13-f-unshift-fixed-small-power-w-gcd/receipt.json
```
