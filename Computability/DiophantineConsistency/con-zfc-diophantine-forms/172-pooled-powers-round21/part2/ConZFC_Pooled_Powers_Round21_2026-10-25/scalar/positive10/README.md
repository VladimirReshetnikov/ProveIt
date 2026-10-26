# Ten positive integers: degree214 in87 operations

Three literal ordinary integer-polynomial equations, all on **ten strictly
positive integer unknowns**, with the same complete BFS943/radix67 four-number
tuple:

| File | Exact degree | Live binary gates |
|---|---:|---:|
| positive10_degree240_ops82.json |240|82|
| positive10_degree232_ops85.json |232|85|
| positive10_degree214_ops87.json |214|87|

The principal214/87 improves the incoming trace232/87 by eighteen degrees;
232/85 saves two gates at that incoming degree. The240/82 equation is a
separate lower-cost tradeoff. These are not unrestricted-integer equations.

`PROOF.md` gives the complete polynomial definitions and ordinary proof;
`MATHEMATICAL_REVIEW.md` independently audits the changed unbounded argument.
The key new bound permits auxiliary index3 and removes T+alpha: the linear
trace gives |b|>4g before the signs of R,B,C are known. The inverse correction
has a favorable sign for every R. Missing divisibility is recovered only
after the full-product projection proves q a power of two.

ZFC proves absence of positive zeros equivalent to syntactic Con(ZFC), at the
explicitly retained native/refutation calibration. No consistency proof,
global minimality, or new end-to-end proof-assistant object is claimed.

```sh
python -B build.py --check
python -B verify.py --deep --mutations --receipt CHECK_DEEP.json
python -B -O verify.py --deep --mutations --receipt CHECK_OPTIMIZED.json
python -B replay.py
```

The independent checker imports no producer. It covers every actual gate,
records complete highest forms, reconstructs all four actual fixed numerals,
and rejects508 altered operation labels. Normal and optimized deep receipts
are byte-identical. The source closure is explained in `CLOSURE_MAP.md`.
