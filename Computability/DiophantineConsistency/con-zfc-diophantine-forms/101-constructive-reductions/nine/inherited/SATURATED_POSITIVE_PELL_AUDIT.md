# Independent audit: a saturated positive ProductPell certificate

This note audits an algebraic modification suggested by the coordinating
research agent. It proves the ordinary mathematical equivalence below. It
does not claim a Lean verification or a new calibration from machine runs to
ZFC refutations.

## Exact theorem

Write `psi_A(0)=0`, `psi_A(1)=1`, and
`psi_A(n+2)=2 A psi_A(n+1)-psi_A(n)`. Its companion is
`chi_A(0)=1`, `chi_A(1)=A`, with the same recurrence. Let

```
A >= 2, B >= 3 odd, C >= B, J >= 1.
```

For positive integers `i,j`, define the following integer polynomials:

```
D = (A^2-1) C^2 + 1,
F = (A^2-1) D (i J C^2)^2 + 1,
L = C D + 1 - A,
G = A + F L,
H = C + F (B + (j-1) C),
I = (G^2-1) H^2 + 1.
```

Then

```
C = psi_A(B)  iff  there exist positive i,j with D F I a square.
```

The original positive certificate used
`F_old=(A^2-1)(i_old J D C^2)^2+1`. Thus the change removes one
factor of `D` from the square expression defining `F`. It does not introduce
a square-root variable. The square root used below occurs in the proof.

## Soundness

All of `D,F,G,H,I` are positive. In particular `D>A`, hence `L>=C`,
and `G>A>=2`.

The defining equations give

```
F = 1 (mod D),       F = 1 (mod C),       F = 1 (mod J),
G = 1 (mod D),       G = 1 (mod C),       G = A (mod F),
H = C (mod F),       H = B (mod C),
I = 1 (mod D),       I = D (mod F).
```

Consequently `D,F,I` are pairwise coprime. If `DFI` is a square, all three
factors are squares. Let `D=d^2`, with `d>0`, and put

```
E' = i J d C^2.
```

Now `F=(A^2-1) E'^2+1` and `C^2 | E'`. The standard positive Pell
parametrization yields indices `n,m,k` such that

```
C = psi_A(n),   E' = psi_A(m),   H = psi_G(k).
```

Since `C>=B>=3`, we have `n>=2` and `n<C`. The Pell divisibility lemma
`psi_A(n)^2 | psi_A(m) => psi_A(n) | m` gives `C|m`, hence `m>=C>n`.
Also `F=chi_A(m)^2`. Because `G=A (mod F)` and `H=C (mod F)`, recurrence
congruence gives

```
psi_A(k) = psi_A(n) (mod chi_A(m)).
```

The positive Pell congruence classification (the same step-down lemma as
in the original ProductPell proof) gives `k = +n` or `-n` modulo `2m`.
As `C|m`, it follows that `k = +n` or `-n` modulo `C`.

On the other hand `G=1 (mod C)` implies `psi_G(k)=k (mod C)`, so
`k=B (mod C)`. Therefore `B=n` or `B+n=C`, using `1<B<=C` and `0<n<C`.
The latter alternative is impossible: `psi_A(n)=n (mod 2)` implies
`C-n` is even, whereas `B` is odd. Thus `B=n` and `C=psi_A(B)`.

The audit point is precise. In the earlier proof, `D|E_old` was used only
to derive `F=1 (mod D)`. Here that congruence follows directly from the
new polynomial. The step-down proof requires `C^2|E'`, which remains true.
It never requires `D|E'` once the congruence has been supplied separately.

## Completeness, including the absorbed H coordinate

Assume `C=psi_A(B)` and put `d=chi_A(B)`, so `D=d^2`. By periodicity of
the invertible Pell recurrence modulo `J D C^2`, choose `m>0` with

```
psi_A(m) = i_old J D C^2,       i_old > 0.
```

Set `i=d i_old`. Then

```
(A^2-1) D (i J C^2)^2+1
  = (A^2-1) (i_old J D C^2)^2+1
  = chi_A(m)^2.
```

Thus `F` and `G` are exactly the old certificate's values. Put
`H0=psi_G(B)`. Recurrence congruences imply

```
H0=C (mod F),      H0=B (mod C).
```

As `F=1 (mod C)`, the integer `q=(H0-C)/F` satisfies `q=B (mod C)`.
We also have `q>=B`. For a direct bound, `L>=C` gives `G>=FC`, and
`psi_G(B)>=B G` for `B>=2`, so

```
H0 >= B F C >= F B + C.
```

The last inequality follows from `B>=2,C>=2,F>=1`.
The bound `psi_G(B)>=BG` follows at once by induction from the recurrence
and monotonicity: the successive increments from index 1 onward are at
least `G`. Therefore

```
j = 1 + (q-B)/C
```

is a positive integer and `H0=C+F(B+(j-1)C)`. Finally
`I=chi_G(B)^2`, so `DFI` is a square. This completes the proof without
assuming that arbitrary old positive `j` values automatically fit the
new absorbed coordinate.

The mapping `i=d i_old` is a completeness embedding. It is not asserted
to be a bijection between all old and new witnesses: a general new
witness need not have `d|i`.

## Useful unconditional polynomial majorant

Let `S=i J C^2` and `T=A D S`. Direct multiplication gives

```
T^2-D F = D (D S^2-1) > 0.
```

This is valid already for `A>=2,C>=1,J>=1,i>=1`, before any square or
Pell assumption. With `V=TGH`,

```
V^2-D F I
  = (T^2-D F) G^2 H^2 + D F (H^2-1) > 0.
```

These identities support a smaller root majorant, but do not themselves
prove the complete finalizer's required lower gap against its other
radicand. That gap must be proved for the actual chosen final polynomial.

## Prior-art boundary in the inspected snapshot

Repository snapshot:
`c1a102936aca437e9999530a0111e6ddab56dc6d`.

The original positive proof is available at
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/34-integer14/audit/ProductPell.lean.txt`.
The exact roles of `hDE`, `hCCE`, `hFD` and the subsequent index argument
were inspected. Packages 66, 67 and 71, and the incoming radical-guard
nine-positive construction, retain `E=i J D C^2` and its full square.

The incoming `ConZFC_Structural_Reductions_Round11_2026-10-24.zip`
already contains **norm saturation** for a different, signed Sun/Lucas
certificate in ten unrestricted integer variables. Its `lucas` and
`lucas_h1868` modules replace `C^4 D^2 xi^2` by `C^4 D xi^2` and prove
a nontrivial residue-interpolation theorem. Therefore saturation itself
must be credited to that preceding package in this project. The present
contribution is its positive ProductPell transport, the exact absorbed-H
theorem above, and any complete nine-positive equation and majorant
subsequently built from it. No historical first-discovery claim is made.

## Verification scope

`check_saturation.py` independently computes complete Pell witnesses for
three small `(A,B,J)` fixtures, verifies the old-to-new map and the absorbed
H quotient exactly, and checks the unconditional congruences/coprimality
and majorant identities on a finite parameter box. It records sizes instead
of serializing large fixture integers. These are transcription checks;
the universal theorem is the mathematical proof above.
