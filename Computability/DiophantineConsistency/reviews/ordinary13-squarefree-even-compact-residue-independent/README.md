# Independent review of the compact residue restrictions

The displayed residue restrictions follow under their stated hypotheses; no concrete error was found in the two signed main-root cases, mod-8 coordinate conditions, or squarefree exclusions. They are necessary conditions for a hypothetical fixed-compact two-norm zero with `J=1`, not a construction of one or proof that its discriminant is squarefree.

The fixed compact definition gives `q=2^590069`, with residues 2, 5 and 12 modulo 5, 9 and 25 respectively. The pinned graph rows give `X=qw`, `Y=q³s`, `a=Y(X+1)`, `H=4a+3`, and the stated shifted `k` and c. The signed-root congruence used by the packet is inherited from the separately reviewed argument: the main norm yields a signed integer root d, and the actual root equation gives `d-a*c≡X mod H/g` with `g=gcd(s,3)`. Thus `5 | H` also gives the congruence modulo 5.

At `5 | H`, `a≡3`, so the Pell multiplier is zero modulo 5. The two possible signs give `d-a*c≡2^m` and `d-a*c≡-2^(-m)` respectively. Independently enumerating these powers gives the four printed `(w,s)` rows: `(0,1)` has no phase; `(1,2)` permits either sign for `m≡1`; `(3,3)` permits positive sign for `m≡0` and negative sign for `m≡2`; `(4,4)` permits either sign for `m≡3`, all modulo 5 or 4 as appropriate. Thus only `(3,3)` remains when m is even. The cases describe phases modulo 4; in particular `m≡0` does not assert the actual positive main index is zero.

Since q is a large power of 2, `Y≡a≡0 mod 8`. The main Pell matrix therefore has multiplier 2 and discriminant 3 modulo 8, and the ordinate sequence has period four `0,1,4,7`. For even m this gives `c≡2m mod 8`, and the literal `c=n_eta+Y*k` gives the stated restriction on `n_eta`. The conclusion that `n_zeta` is odd also uses the separately reviewed first-norm classification making k even; it does not follow from the main norm alone.

For the squarefree tests, modulo 9 and 25 the factors `a+1` and `a+3` cannot both be divisible by the relevant prime. Solving the two divisibility congruences gives precisely the excluded inner residues `{1,3}` modulo 9 and `{8,24}` modulo 25. Modulo 3, `Delta` is nonzero exactly for `a≡1`; the additional assumption `gcd(m,Delta)=1` forces `3 ∤ m` otherwise. The listed `(w,s,m,n_eta,n_zeta)=(3,8,4,0,1)` satisfies the local checks, but does not demonstrate a full norm solution or squarefreeness.

The independent checker pins the packet and graph, verifies the actual graph operands, enumerates both signs from powers rather than repeating the packet's Pell-iteration method, checks the full mod-8 period and exhausts both prime-square residue grids. These checks corroborate the derivation; the signed-root and first-norm classifications remain the explicitly identified standard-integer inputs. No Lean, build, staging, arbitrary-model transfer or provider validation was run.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-squarefree-even-compact-residue-independent/check.py | cmp - reviews/ordinary13-squarefree-even-compact-residue-independent/receipt.json
```
