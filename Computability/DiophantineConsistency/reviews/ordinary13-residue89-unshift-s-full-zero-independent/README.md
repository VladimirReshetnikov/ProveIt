# Independent review of the unshifted-s full-zero probe

The probe removes exactly `shift_s=n_s+1` from the pinned 13/89 graph and substitutes `n_s` for every use; its 88 rows are otherwise identical. A separate exact sparse-polynomial evaluation confirms that all four residuals and the output vanish identically for the proposed five-parameter family with `n_s=0`. The checker independently authenticates the compact P72 and P115 port hashes and verifies the inequalities needed to make the family a nonnegative witness. The original source receipt reproduces too.

The arithmetic is valid for every `beta>=3` and natural K0, MC, MF. With `h=ceil((K0+2)/beta)`, `X=beta*h-K0-1>=1` and `t=(beta-1)*h-1>=1`. The constructed R is positive, P=beta*t is positive, and `r=(R+1)*(P-1)+t+1` is positive; hence all shifted and unshifted input coordinates are natural. The compact bytes meet these assumptions. The polynomial evaluation makes the conclusion exact, without displaying or directly expanding the several-million-bit witness coordinates.

Thus the probe has a full standard-natural zero even at the authenticated compact ports, so its equations do not force s positive. The unchanged parent graph evaluated at the same witness is a separate question; a toy instance shows this particular same-coordinate transport can fail, but the full-zero family does **not** establish that the probe and parent differ in global zero existence. It supplies neither an iPRA equivalence nor a Lean proof, and does not bind the maintained current-2011 PDF.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue89-unshift-s-full-zero-independent/check.py | cmp - reviews/ordinary13-residue89-unshift-s-full-zero-independent/result.json
python3 -I -S -B research/ordinary13-residue89-unshift-s-full-zero/check.py | cmp - research/ordinary13-residue89-unshift-s-full-zero/receipt.json
```
