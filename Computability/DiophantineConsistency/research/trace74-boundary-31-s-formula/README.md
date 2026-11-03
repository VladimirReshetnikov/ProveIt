# Compact expression for the R=31 partial seed's s

The audited partial seed in `../trace74-boundary-31-seed/observation.json` uses a 462-bit positive integer `s`. With `X=2^31`, exact integer division gives

```
s = floor((X+1)^30 / (16*X^15)).
```

`check.py` pins the unchanged seed observation and verifies the quotient, remainder bounds and division identity using exact integers. The observation records the result. This is a finite external identity; it is not a Lean certificate, a graph zero, a fixed-port result or an iPRA theorem.
