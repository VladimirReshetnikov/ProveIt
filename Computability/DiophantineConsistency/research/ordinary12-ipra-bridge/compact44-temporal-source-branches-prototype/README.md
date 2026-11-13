# Exploratory fractional temporal cyclic-source branches

For any IΣ₁ model, the three sources prove the actual temporal radix-67 digit formula in the branches q<t, t<q, and q=t, respectively. Each assumes `t<n`, `0<r<67`, `E%(67*n)=67*q+r` (with q=t in the final branch), and the explicit word bound where needed. With `j=cyc n t q`, the result is

```text
dig 67 (rot 1 (67*n) X (E%(67*n))) t =
  (dig 67 X j * 2^r) % 2^67 + dig 67 X (cyc n j 1) / 2^(67−r).
```

The straddling branch uses the actual last source digit at the word boundary; zero padding beyond n is not identified with cyclic wrap. The aligned r=0 formula was separately explored in commit 81417adafb. A single theorem covering all cases and the graph-selected target/predecessor has not yet been compiled.

The final author-only sessions 26724, 15976 and 9228 actually exited 0 without warnings or `sorryAx`; axiom reports use `propext`, `Classical.choice`, `Quot.sound`. Earlier sessions and exact logs are retained: 38143, 83849, 32595 and 36252 failed, while 72672 exited 0 with one unused-variable warning and 8796 used that warning-bearing object; both were superseded by the final rebuild. These are exploratory single-side results on the author overlay and prior dependencies in ae249d0592, ffe7765fba and 81417adafb, not a paired replay or independent artifact audit. No clean-carry, graph-column, retained-K or iPRA result is claimed.
