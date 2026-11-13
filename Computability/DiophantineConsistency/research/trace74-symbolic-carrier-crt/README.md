# A scalar CRT extension through carrier divisibility

This ordinary-integer argument extends the fixed symbolic-beta scalar
candidate in the [Pell/projection obstruction](../trace74-symbolic-pell-projection-obstruction/README.md).
It shows that several additional **necessary** conditions for a graph
zero can hold together while the reverse guard fails. It does **not**
construct a graph zero, satisfy the final carrier norm, or prove anything
in Lean or iPRA. In particular, the remaining coupled equations for
`V`, `Z`, `Q`, and the adjustable witnesses may still rule it out.

Use the sibling candidate's exact values

```text
B=590069, q=2^B, h=q−1, J=1,
n=3054883185, r=3056651345, X=2^r, Y=q³, w=X/q.
```

Let `k,c` be its actual first and main Pell ordinates, and `eta,zeta`
the positive split for which `k=eta+zeta` and `c=kY+eta`. Put
`D=XY`, `H=4Y(X+1)−1`, `Kreg=X(3c−2X)+2`, and choose `F=1`.
The first port is the symbolic `beta=q−1`. For concreteness the
external `K0` is the little-endian value of the retained `K.bin.gz`
payload with raw SHA-256
`0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f`;
the connection of that file to a Lean symbolic port is **not** proved
here. Let `MC,MF` be arbitrary natural numbers, and put `RJ=MC+q MF`.

The sibling's exact modular Pell computation establishes
`gcd(c,q²−1)=1`. Since `r` is odd, the Pell recurrence also gives
`c≡r (mod q³)`, so `c` is odd. Therefore `D`, `c`, and `h` are pairwise
coprime: `D` is a power of two, and `h` divides `q²−1`. The finite
checker here reads the hash-pinned external `K0` and verifies

```text
gcd(H,h)=gcd(4·2^93925+3,2^590069−1)=1,
gcd(K0+w,h)=gcd(K0+2^93925,2^590069−1)=1.
```

It follows that `gcd(H,hD)=1`: `H` is odd and `D` is a power of two.
All statements concerning the huge Pell ordinate rely on the sibling
GMP computation and its source, not on materializing `c` here.

## Prescribing the signed rank and the carrier residues

Set `R=(q²−1)G+RJ`, `C=q(q−1)−G`, `e=k−R−1`, and
`Breg=(K0+w)C−1`. Each coefficient below is invertible modulo its stated
modulus: `q²−1` modulo `D` and `c`, and `K0+w` modulo `h`. By CRT, there
is an integer `G` satisfying

```text
R ≡ k−1 (mod D),      R ≡ −r (mod c),
(K0+w)G ≡ −1 (mod h).
```

Shifting `G` by a sufficiently large negative multiple of `Dch` retains
the congruences and ensures `G<0`, `R<0`, `C>0`, and `Breg≥0`. Consequently
`F+C≥q`, so the reverse guard fails. Since `R<0`, the middle congruence
gives `|R|≡r (mod c)`, one branch of the main-index `SignMod` condition.
The first congruence gives `D|e`; as `r≥B` and `D=2^(r+3B)`, it also
implies the weaker previously checked `q⁴|e`. The third congruence and
`C≡−G (mod h)` give `h|Breg`. These are existential ordinary-integer
choices: the enormous values of `G`, `C`, and `c` are not printed.

## Why the carrier register is divisible

For the actual register shapes, write `v7` for the free natural coordinate
and `V` for the signed graph register:

```text
Z=hD[H(v7−V²Breg)+Kreg]−H(DBreg+h e),   M=hDH.
```

The two CRT consequences give `hD | DBreg+h e`. Also `H|Kreg`. To see
the latter, set `a=Y(X+1)−1`, so `H=4a+3`. For Pell coordinates with
base `a+2`, put `d_j=x_j−a y_j`. The recurrences give `d_0=1` and
`d_(j+1)=2d_j+H y_j`, hence `x_r≡2^r+a y_r=X+a c (mod H)` by ordinary
induction. The Pell norm then gives
`H | X²+2aXc−1`. Since

```text
Kreg = H X c − 2(X²+2aXc−1),
```

`H|Kreg`. Both parts of `Z` are therefore divisible by `hDH=M`, for
any values of `V` and `v7`. The independently checked `gcd(H,hD)=1`
also justifies the reverse inference from `M|Z` to
`hD|DBreg+h e` for this candidate. This is **divisibility only**: it
does not assert the quotient equals the required `±tau f y` or that the
adjacent Pell norm holds for the actual `V`.

## Checks and boundaries

From the repository root,

```text
python3 -I -S -B Computability/DiophantineConsistency/research/trace74-symbolic-carrier-crt/check.py
gcc -O2 -Wall -Wextra Computability/DiophantineConsistency/research/trace74-symbolic-pell-projection-obstruction/pell-gcd.c -lgmp -o /tmp/trace74-crt-pell-gcd
/tmp/trace74-crt-pell-gcd
```

The Python check pins the external 74-row candidate JSON and compares its
port order, witness order and four coefficient metadata entries to the
available compressed/raw payloads and hashes. It verifies their bit
lengths, the exact external beta value, and the two stated symbolic gcds.
It also tests the CRT, sign and actual `M|Z` register identity for the much smaller
analog `B=7,n=63,r=77`. The GMP program computes only
`gcd(c,q²−1)` for the symbolic candidate. Neither check is a Lean proof,
an exhaustive verification of the displayed symbolic construction,
or a check of all graph factors. The metadata comparison is not a formal
Lean semantics for the external JSON.
