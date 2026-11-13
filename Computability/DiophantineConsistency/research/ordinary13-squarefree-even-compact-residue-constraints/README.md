# Compact-port restrictions on the even-index squarefree branch

Suppose, conditionally, that the actual shifted nine-variable two-norm graph has a standard-natural zero at the fixed compact tuple with `J=1`, and let m be its positive main Pell index. If m is even, then

```text
n_eta ≡ 2m (mod 8),       n_zeta is odd.
```

If in addition the actual main factor H is divisible by 5, the only possible residue pair is `(w,s)≡(3,3) (mod 5)`. Its main root is positive only when `m≡0 (mod 4)` and negative only when `m≡2 (mod 4)`. Here `w=n_w` and the displayed `s=n_s+1`. These are necessary conditions, not a construction of a compact two-norm zero.

If the discriminant `Delta=(a+1)(a+3)` is squarefree, two further necessary conditions are

```text
s*(5w+1) mod 9  ∉ {1,3},
s*(12w+1) mod 25 ∉ {8,24}.
```

If also `gcd(m,Delta)=1`, then `3 ∤ m` whenever `a≢1 (mod 3)`. These statements do not establish squarefreeness or the coprimality hypothesis for any actual witness. The [general squarefree obstruction](../ordinary13-parent-even-index-squarefree-same-data-obstruction/README.md) remains conditional; it rules out a specified same-data parent completion, not all possible witness changes or all graph zeros.

## Actual root phase modulo 5

For the compact beta and J=1, `q=2^590069≡2 (mod 5)`. At a main-norm zero the [separately reviewed signed-root argument](../../reviews/ordinary13-shifted-two-norm-lift-obstructions-independent/README.md) gives `d−a*c≡X (mod H/g)`, where `g=gcd(s,3)` and d is either sign of the main Pell abscissa x. If `5 | H`, then `5 | H/g`. With `X=qw` and `a=q³s(X+1)`, the condition `H=4a+3≡0` is exactly `s*(2w+1)≡1 (mod 5)`. The four resulting pairs and their exact signed Pell congruences are:

| w mod 5 | s mod 5 | allowed m mod 4 and sign |
| ---: | ---: | --- |
| 0 | 1 | none |
| 1 | 2 | 1, either sign |
| 3 | 3 | 0 for positive d; 2 for negative d |
| 4 | 4 | 3, either sign |

The table follows from `x−a*c≡2^m` and `x+a*c≡2^(−m)` modulo 5, then using the actual signed root; it handles both signs. Thus an even m forces the third row, refining the earlier w=1 obstruction. All of this is conditional on `5 | H`; it says nothing about other H residues.

## Modulo 8 and squarefree local conditions

The fixed power q is even, so `Y=q³s` is divisible by 8 and `a=Y(X+1)≡0 (mod 8)`. The main Pell transition matrix is `[[2,3],[1,2]]` modulo 8. Its fourth power is the identity, and the first four ordinate residues are `0,1,4,7`. For even m this gives `c≡2m (mod 8)`. The actual graph equation `c=n_eta+Y*k` gives the first displayed restriction. At a two-norm zero, the first Pell ordinate k is even by the separately reviewed first-norm argument. Since `k=n_eta+n_zeta+1` and n_eta is even, n_zeta is odd.

Both `a+1` and `a+3` are odd and differ by two, hence are coprime. Squarefreeness of Delta requires neither factor be divisible by 9 or 25. Since `q≡5 (mod 9)` and `q³≡8 (mod 9)`, writing `u=s*(5w+1)` gives `a≡−u (mod 9)`, so the two forbidden residues are u≡1 and u≡3. Similarly `q≡12 (mod 25)` and `q³≡3 (mod 25)` give `a≡3*s*(12w+1)`; the two forbidden residues of that inner product are 8 and 24. Modulo 3, `(a+1)(a+3)` is nonzero exactly when `a≡1`; hence the separate coprimality hypothesis forces `3 ∤ m` in either remaining case.

The local conditions alone do not exclude the branch: `(w,s,m,n_eta,n_zeta)=(3,8,4,0,1)` satisfies the displayed mod-5, mod-9, mod-25 and mod-8 restrictions, and Delta is automatically odd so `gcd(4,Delta)=1`. This is **only a residue assignment**; it is not asserted to satisfy either graph norm, to make Delta squarefree, or to be a parent or child zero.

The source checker pins the relevant literal graph, compact beta and both prior arguments. It exhausts the relevant finite residue classes and checks the Pell matrix period modulo 8. These computations verify the displayed local arithmetic, while the conditional derivation still uses the stated standard-integer Pell and signed-root facts. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-squarefree-even-compact-residue-constraints/check.py | cmp - research/ordinary13-squarefree-even-compact-residue-constraints/receipt.json
```

No Lean, build, staging, nonstandard-model transfer, provider audit, or iPRA claim is made.
