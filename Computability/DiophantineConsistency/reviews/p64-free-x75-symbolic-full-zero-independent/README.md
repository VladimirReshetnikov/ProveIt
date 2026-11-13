# Independent free-X symbolic zero and forward-map review

The [free-X full-zero construction](../../research/p64-free-x75-symbolic-full-zero/README.md)
and [graph/forward binding](../../research/p64-free-x75-graph-binding/README.md)
check out mathematically within their stated external scope. The modified
75-gate graph has the specified full positive zero at the stated natural
ports with `q=3` and `w=8`; the simple inverse that keeps `w/q` fails there.
This does not rule out another original witness at those ports, settle
existence equivalence, address compact44 ports, or prove an iPRA theorem. No
Lean or enormous strong/auxiliary coordinate was evaluated.

[`check.py`](check.py) independently bounds the two positive Pell
coefficients using outward-rounded 384-bit pair powers and verifies
`27k<c<28k` without radicals or full coordinates. It independently checks
the main residues by matrix powering and verifies divisibility of the main
carrier and `gamma`. The pair bounds are sound by componentwise positivity,
exact exponents, and directed truncation. Finite Chebyshev cases are only
sanity controls; the universal recurrence and norm proof is reviewed below.
Exact source pins and outputs are in [`result.json`](result.json).

The ratio makes `eta,zeta>0` and reproduces `c`; both Pell norms give the
first and main factors. As `g−X−ac≡0 (mod H)`, `A` is an integer multiple of
`U`, and the checked residues `k≡454`, `m≡453 (mod U)` make `gamma` an
integer. It is positive because `k≥2j>m` and `g>(n−1)c>X+ac`.
For the specified small inputs, `R=m` and `Lt=0`; the carrier becomes `Ug`,
so `M=0`.

The binomial expansion of `(g+c√D)^c` gives `c²|L`; the norm then proves
`I=i c²=DL` and `W=0`. Since the auxiliary exponent `m` is odd, its first
coefficient is divisible by `I`, and its Pell norm implies `Na=1`. The
identity `T_(2r+1)(x)/x` evaluated at `x²=1−n²` equals `(−1)^r U_(2r)(n)`:
both sides have equal first two terms and obey the same second-order
recurrence. As `m≡3 (mod 4)`, this yields `V≡−c (mod f²)` and the positive
integer `Q=(c+V)/f²`. Since `c²|I`, `V≡−m (mod c)` from the constant term;
`f²≡1 (mod c)` then makes `T=(m+Q)/c` a positive integer. Thus the actual
graph expression `f²(cT−R)−c` equals `V`, and all five required residual
conditions hold.

The graph transformation deletes only `X=w*q`, substitutes its input `w` in
`E` and `b0`, and leaves all 75 gates live. The author's structural binding
result reproduces byte-for-byte; its 21 formula checks and symbolic transport
identity were source-reviewed. Independently, [`check_graph.py`](check_graph.py)
tests the exact graph rewrite, its topological order and liveness, 200 direct
forward-map valuations, and the displayed small witness core. For a positive
old zero, old transport implies `C=q−F−alpha>0`. Setting `w'=q w` and
`z'=z+w C` keeps every other residual equal and preserves positivity, since
`(K+w')C−F−z'(q−1)=(K+w)C−F−z(q−1)`. This is a mathematical forward map,
not a Lean theorem; the numerical tests alone do not prove it universally.

Reviewed binding README, checker, and result hashes respectively:
`6022b5c7e5878b86942cdaf0dde5c6f2aa390430c65cde18326679a85f4ac22c`,
`416b337b0bbb616bf1c9fcaa42d4301e3546a61726bb6fd9501202985b7f0490`,
`242051c33a3fb6c69cb713334e21593f0e90df5192b2f672912e238361aaf68b`.
Run each independent script with `python3 -I -S -B`.
