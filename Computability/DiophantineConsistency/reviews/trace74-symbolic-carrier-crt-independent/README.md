# Independent arithmetic review of the carrier CRT extension

The reviewed [note](../../research/trace74-symbolic-carrier-crt/README.md)
has SHA-256 `ab3f8afaeb76e3062bf2e41a2fe5119c76b637018173cc37240e9b74463200db`;
its [checker](../../research/trace74-symbolic-carrier-crt/check.py) has
SHA-256 `781c98e89187dfbb1b6f4a440161007367d17289b784a4691d1ada4c7d65be31`.
The ordinary-integer proof is valid under its stated fixed candidate,
external coefficient choice, and finite gcd results. This review does not
assert a full graph zero.

The CRT moduli are pairwise coprime: `D=XY` is a power of two, the odd
index and even Pell coefficient make `c` odd, `h=q−1` is odd, and the
separately computed `gcd(c,q²−1)=1` implies `gcd(c,h)=1`. The coefficient
`q²−1` is invertible modulo both `D` and `c`; the checker establishes
invertibility of `K0+w` modulo `h` for the chosen hash-pinned external
`K0` and actual `w=X/q`. CRT therefore allows the stated three congruences
for one `G`. Shifting by a sufficiently negative multiple of `Dch`
preserves them and makes `G,R` negative. This simultaneously gives
`D|e`, `h|Breg`, positive `C`, guard failure, and the stated `SignMod`
branch. Since `r≥B`, `q⁴|D` also holds.

For `a=Y(X+1)−1`, `H=4a+3`. The checked Pell projection recurrence
gives the main abscissa `d≡2^r+a c=X+a c (mod H)`; its norm yields
`H | X²+2aXc−1`. The exact identity

```text
Kreg = H X c − 2(X²+2aXc−1)
```

therefore proves `H|Kreg`. Also `D|e` and `h|Breg` imply
`hD | DBreg+h e`. Both terms in the displayed `Z` register are then
divisible by `M=hDH`. This argument uses the actual `w=v 5=X/q` and
does not impose any unproved choice of `V` or `v 7`.

The reviewed checker was rerun with `python3 -I -S -B` and exited 0,
including its pinned 74-candidate metadata, all four compressed/raw payload
hashes, the beta identity, and its exact small `B=7` CRT and carrier test. The payloads'
declared roles match the separate decimal display generator; this source
review does not itself prove those generated constants equal Lean ports.
Separately, an
alternate Python calculation using modular `pow` and `math.gcd` exited 0
in tool session 45138: it authenticated the declared decompressed `K0`
hash and independently obtained `gcd(H,h)=1` and `gcd(K0+w,h)=1`. These
are external finite computations; they do not authenticate the external
payload's identification with the Lean symbolic port.

`M|Z` alone does not prove the required quotient identity, the remaining
norm equations, or the graph output is zero. This is a mathematical and
executable source review, not an independent Lean replay, a proof of a
full graph witness, or an iPRA endpoint.
