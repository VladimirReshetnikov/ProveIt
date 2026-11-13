# Corrected finite prime screen for matched-index offsets

For the fixed compact ports and \(J=1\), put \(d=L-h\),
\(m=n+d\), and require the exact matched rank \(R=2n-1\). The
power match gives

\[
(h+1)n=(L-h)(2L-h+1).
\]
Expanding this equality and completing the square yields

\[
(4L+1-3h)^2=(h+1)(h+5+4R).
\]
Thus, for any prime p, a necessary condition is that the right side be a
quadratic residue modulo p. The factor \(h+5\) is essential; an earlier
informal calculation incorrectly used \(h+1\) in its place. For \(h=1\),
the correct expression is \(8R+12\), matching the separate earlier proof.

The [source-pinned earlier certificate](../ordinary13-i-unshift-fixed-shifted-power-modular-obstructions/README.md)
checks that \(p=193707721\) is prime and that at the exact compact ports
with J=1, \(R\equiv55801659\pmod p\). Among integers \(1\le h\le30\),
excluding the residue classes already ruled out by the separate mod-3 proof,
the correct prime test gives:

| Status of necessary square condition | h |
| --- | --- |
| Nonsquare; exact power match excluded | 1, 7, 10, 16, 19, 26, 28 |
| Square or zero; this necessary test passes | 4, 8, 13, 17, 22, 25 |

Passing the test does not construct a witness or establish that any graph has
a zero. Failure rules out only this exact index/rank matching for the specified
fixed ports and J=1; other J, rank shifts and witness maps are not excluded.
No Lean, iPRA or all-model theorem is claimed.

The checker replays the pinned earlier source checks, computes the corrected
Euler criteria, and tests the completed-square identity on bounded controls.
The displayed expansion is the general proof. Run from
`Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-i-unshift-shifted-offset-prime-screen/check.py | cmp - research/ordinary13-i-unshift-shifted-offset-prime-screen/receipt.json
```
