# Independent audit: fixed-point full child witness

The reviewed `research/ordinary13-independent-k-fixedpoint-full-zero/` gives a mathematically valid **standard-integer symbolic zero** for the 84-operation independent-k child at its fixed symbolic compact tuple, with eta>k, subject to the pinned arithmetic source recipes and the stated finite Pell constructions. This rules out pointwise forcing `k≥eta` for that child. It does not settle whether its parent has a zero, rule out a different existential witness map, prove anything about the maintained displayed equation, or provide a Lean or iPRA theorem.

The independent residue packet reconstructs the four compact ports and K′ modulo `N=590069` from all 943 ordered source rows, the 41 slots and the exact mask digit recipes. It independently finds the map `R(e)≡365222−460162*2^e (mod N)` and checks the fixed point `e=439547`. This review additionally checks all N candidate exponents and finds no other fixed point, and reproduces the author's receipt. Only the one verified fixed point is needed for the construction; no giant fixed coefficient is materialized.

With `q=2^N`, `beta=q−1`, `K0=beta*rho^42+K′`, `F=K′+2^e`, `alpha=beta−F`, and J=s=1, the pinned kernel bound `K′<2^368232`, together with `368232<e<N−2`, gives positive F and alpha. The actual graph has `C=1`,

```text
G=alpha+(q−F)*beta=q²−1−q*F,
R=G*(q²−1)+MC+q*MF.
```

Because `q−F=alpha+1≥2`, `G≥2q−1`, hence `R≥q³>N+e` for this q. The low digit and q divisibility give `R≡3 (mod 4)`, so `n=(R+1)/2` is an integer at least 14. Set `w=2^(R−N)` and `X=q*w=2^R`. The fixed point gives `R−N≡e (mod N)`, and hence `z=(w−2^e)/beta` is a nonnegative integer. Direct algebra with `h=w+rho^42+z` gives the actual first carrier `B=beta*h`.

For `Y=q³`, `M=X*Y²` and the nth Pell pair at multiplier `2M+1`, set `k=2*yFirst`. Its norm gives `tau²=1+M*(M+1)*k²` and its recurrence gives `k=2n+4M*sFirst` for a natural quotient. With `ell=M*k`, the stated `rWitness=tau−ell−k+(k*beta+1)*h` is natural because tau>ell and beta,h≥1. Exact independent integer-polynomial normalization confirms that the graph's signed first root is `beta*tau`, giving A0=0.

Set `a=Y*(X+1)`, `H=3+4a`, and let `(g,c)` be the Rth Pell pair at multiplier `a+2`. The recurrence bounds give `k≤2*(6Xq⁶)^(n−1)` and `c≥(Xq³)^(2n−2)`. For X≥q≥24 and n≥14, `q^(n−4)>4*6^(n−1)` implies `c>(q³+1)k`; thus `eta=c−Y*k` is natural and exceeds k. Independently, `c≥(X*Y)^(2n−2)>X` because `n≥2`, `X≥1`, and `Y>1`. The recurrence identity `g−a*c≡2^R=X (mod H)` and `g−a*c≥c>X` make `(g−X−a*c)/H` a positive integer. The **generalized-X** scale is essential:

```text
gamma = 4*X*q*sFirst + (g−X−a*c)/H
      = 4*q²*w*sFirst + (g−X−a*c)/H,
```

because `M/U=Xq` for `U=q⁵`. The exact polynomial check confirms that the literal main root then equals U*g, so A1=0.

The independently reviewed strong/auxiliary construction applies unchanged: a finite positive Pell-matrix period modulo c² gives positive f and i with `I=i*c²` and strong residual zero. Since R≡3 mod 4, the odd-index polynomial identities and CRT produce a positive T and an auxiliary Pell ordinate for which the exact graph auxiliary factor is one. All four product factors are therefore one for the displayed 13 natural inputs.

The reproducible checker pins the independent fixed-point and auxiliary reviews, the candidate and the author's finalized certificate; checks exact graph rows, first carrier/root and generalized main scaling as formal integer polynomials; independently exhausts the fixed-point congruence; and runs bounded growth controls. The uniform growth, finite-period and CRT arguments are mathematical proofs, not consequences of those finite controls. Neither this review nor the author packet executes Lean, selects providers, audits axioms or proves an arbitrary-model interpretation.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-independent-k-generalized-witness-independent/check.py | cmp - reviews/ordinary13-independent-k-generalized-witness-independent/receipt.json
```
