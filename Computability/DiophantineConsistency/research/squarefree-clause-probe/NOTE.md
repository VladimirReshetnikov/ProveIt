# Squarefree composite length2983

This isolated probe retains the entire center1956 parity geometry and
all942 admissible coefficients from `../parity-clause-probe/`. It changes
the whole cell length from the prime2999 to `L=2983=19*157`. The binary
exponent is `d=47L=140201`, still odd and squarefree. Every prime divisor
of d is included in the controller; no primality assumption on L is used.

The four complete unsigned big-endian ports total70,157 bytes,376 below
length2999 and1,268 below the first single-clause length3037. Their bit
lengths are140201,140625,140201,140202 for beta,K,MC,MF_source. The lower
padding endpoint remains2962 and its highest field2981 remains below L.
The whole field geometry, all1006 low reflected arrays, all978 coarse
marker offsets, all934 fine offsets, Boolean-tau count cases, masks,
rank identities and safe-dummy margins are recalculated at this length.

The complete fixed controller is:

| Prime | ord(2)=ord(B) | B | K | B² | 1+BK+B² |
|---:|---:|---:|---:|---:|---:|
|47|23|18|41|42|29|
|19|18|10|5|5|18|
|157|52|41|140|111|43|

The order spacing is `lcm(23,18,52)=10764`, coprime to d. Complete
proper-order checks use23, then2/3, then2/13 respectively. Elementary
trial division proves all three prime factors; their product is exactly
d. The auxiliary prime is `lambda=150697=14*10764+1>d`. There,
`B=110491`, `K=71057`, `B²=146414`, and `H=142399`. The lift
`2^(d*(lambda-1)) mod lambda²` is412909781, with nonzero quotient2740
after subtracting one and dividing by lambda. The required valuation is
therefore exactly one.

The deterministic search starts at2982, rejects that even length, and
accepts2983 after checking every prime divisor of d. This is the first
odd squarefree length that can hold this fixed padding; it is not a
global lower bound on alternative encodings. Dense Phi evaluation, the
direct complete942-tile/34-label expansion, and the whole integer K
agree at every fixed and auxiliary prime. All four stored constants
are rebuilt together.

The exact source binding, all3297 coefficients, scoped negative controls
for center1955 and marker1004, and finite-only review boundary are as
documented in the parity probe. Run `python probe.py` and
`python -O probe.py` to check the deterministic receipts; `--write`
regenerates them. The separate complete ordinary proof must explicitly
use all three prime divisors of d before this variant can be promoted.
