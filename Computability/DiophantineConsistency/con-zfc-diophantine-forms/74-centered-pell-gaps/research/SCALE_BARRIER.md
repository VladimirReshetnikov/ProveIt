# Why the cubic scale on the half-binomial ordinate cannot simply be transferred

Source snapshot: `9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`.

Primary repository sources:

- `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md`, section 2 (Git blob `90aa8895f38e2f9cb3a13c7ecff9f3f2a8d1fbf3`).
- `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_asymmetric_scale_tradeoffs.md`, section 4 (Git blob `db70d23cd1e9a03be0ea7a70a4be1b61f71e77d5`).
- `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_asymmetric_scale_transfer.md`, sections 2--4 (Git blob `d5939687bc38217505f0ef86730b8cfff467fc2c`).

Write `pc` for binary population and let `q=2^t`. The native compiler packs two q-bit words into `S`, and its two masks into `T`, with

    1 <= S <= q^2, 0 < T < q^2-1, pc(T)=t+2,
    R=(q^2-S)(q^2-1)+T.

The exact inverse-population lemma is

    pc(R) <= 3t+2,

with equality precisely when `S<q^2` and `S AND T=0`. The population test therefore must detect this maximum. In the half-binomial construction the relevant ordinate valuation is `pc(R)-2`; requiring `q^3 | Y` supplies precisely the threshold `3t`.

The initially tempting change `X=wq,Y=sq^3` to `X=wq^2,Y=sq^2` retains `XY>=q^4`. It preserves the coarse bound used to rule out an index wrap. It does not preserve the population test: `q^2 | Y` only asks for `pc(R)>=2t+2`.

## Exact local negative control

Take

    q=16, t=4, S=32, T=175.

Then `pc(T)=6=t+2` and

    R=(256-32)*255+175=57295,
    R mod 4=3,
    pc(R)=13,
    S AND T=32.

The correct threshold is 14 and rejects this overlap. The weakened threshold is 10 and accepts it. This example is only a counterexample to the weakened *packing predicate*. It does not claim a solution of the complete ZFC-consistency polynomial.

More generally, adding a one-bit S that meets an isolated one-bit of T creates one carry and lowers the population by just one. There is no general gap of t population units that could make the weaker threshold equivalent.

## What remains possible

A new compiler could lower the threshold by reducing the packed word width or the mask population. That requires a new simultaneous representation of both native typing and field conditions. Merely moving factors of q between the two Pell coordinates, or recovering that X is a power of two, does not establish it. The existing asymmetric-scale theorem explicitly retains the cubic scale on Y for this reason.

The source-level alternate approaches inspected (small universal machines with fixed nonblank input, word/matrix-semigroup reachability, and one-stack numerical proof certificates) do not yet yield a smaller completed ordinary polynomial: each still needs the full fixed-arity unbounded-history compilation. In particular, a linear equation over a finitely generated matrix monoid is not a linear Diophantine equation over arbitrary integer entries; monoid membership carries the computation.
