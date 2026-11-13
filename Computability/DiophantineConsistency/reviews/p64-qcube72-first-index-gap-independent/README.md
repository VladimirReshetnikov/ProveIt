# Independent review of the 72 first-index gap analysis

The corrected [analysis](../../research/p64-qcube72-first-index-gap-analysis/README.md) is valid in the stated integer and conditional scope. In particular, the carrier-scale and shape results alone do not supply the Pell indices: the argument also needs the positive Pell-classification step, an extracted graph carrier and the stated norm hypotheses. The 72 graph-specific client remains unchecked in the cited packet.

Assuming `m=R`, positive Pell coordinates and `Ug=U(X+ac)+Hh`, the pinned projection identity gives `g=2^R+ac+Hz` for a natural `z`. Thus `H | U(2^R−X)`. For `e=gcd(U,H)`, `u=U/e` and `v=H/e`, cancellation yields `v | 2^R−X`; the quotient `d=(2^R−X)/v` may be negative. Substitution then gives the exact integer equality `h=Uz+u d`. The first norm's existing Pell classification and recurrence give `k≡2n (mod U)`, so the old carrier divisibility is equivalent to

```
u d + 2n − R − 1 ≡ 0 (mod U).
```

The cited `P64Early.gcd_dvd_nine` supplies `e | 9`; the derivation does not silently assume `H` and `U` coprime. The linked old-graph index and power theorems have additional hypotheses, including the early congruence and exact first-index relation. The free carrier alone does not establish them. The compact44 discussion is conditional: the half-index theorem still needs its large-`c` and other hypotheses, and no general conclusion about compact44 zeros follows.

The [independent bounded checker](check.py) pins the source interfaces, graph and author screen. It uses a separate deterministic Pollard-rho factorizer (with verified sub-64-bit primality and factor products) to enumerate all possible carrier moduli in the stated finite domain. For `beta=2`, `J=1`, `q=3`, `F=alpha=1`, `R∈{43,47}`, `1≤s≤30`, and `1≤n≤R`, it reproduces exactly two positive-carrier projection candidates:

```
(R,s,w,H) = (47,8,6351,16462659)
(R,s,w,H) = (47,26,10021896201,84424453600035).
```

It checks every first index in that range for both and finds no `Yk<c<(Y+1)k` match. The divisor enumeration is complete for this bounded family because `H | U(2^R−X)` implies `H | U(4Y(2^R+1)+3)`. A failed factorization raises an error rather than omitting a case. This is a small non-compact44 screen; it does not exclude larger `s`, other ranks, first indices beyond `R`, different ports, or a 72 zero in general.

No Lean command was run and no new theorem or existential counterexample is claimed. Existing source/provider ancestry remains as previously recorded.

```
python3 -I -S -B path/to/p64-qcube72-first-index-gap-independent/check.py
```

The deterministic result is frozen in `result.json`.
