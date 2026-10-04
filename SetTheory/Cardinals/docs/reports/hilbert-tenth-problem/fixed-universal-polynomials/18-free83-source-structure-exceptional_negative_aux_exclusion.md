# Excluding the negative auxiliary branch on the genuine compiler slice

This continues `early_auxiliary_norm_lemma.md` and uses only that note's unconditional reduction plus the five-unit arguments already proved in the exact parent85 mathematical review. No normalization of a general candidate zero is assumed.

## Hypotheses recovered only inside the exceptional branch

The full83 product equation and Na<0 force f=1, S=A, norm_strong=-1, Na=-Delta. Consequently the five untouched integer factors have product 1 and each is a unit.

The first norm's negative-unit descent gives norm_first=1; the congruence Delta=0 or 3 mod4 excludes norm_main=-1 and norm_input=-1. Thus those two norms are also 1. Index and transport signs are equal, each ±1.

The exact parent85 review Sections 2 and 4 now apply up through the statements preceding any strong-rank use:

- transport's unit magnitude forces C>=0 and F+Z<q
- genuine shifted compiler mask bounds give 0<R<a<Delta and E>R+2
- the first norm gives k=2 psi_P(n), P=2XY²+1
- the index unit gives 2n=R+epsilon mod E and n>=(R-1)/2>=24
- the positive main root gives c=psi_A(p), p>n, hence p>=25
- c>2R follows from k=R+epsilon+hE, h>=1, E>R+2 and c>kY
- c>A Delta² follows independently from p>=25: psi_A(6)=32A⁵-32A³+6A, and psi_A(6)-A(A²-1)²=A(31A⁴-30A²+5)>0 for A>=2

These are precisely statements of the retained five-unit subsystem. They do not depend on the old strong divisibility, on p=R, or on a complete parent zero.

From the auxiliary classification in the earlier note, set B=2A²-1. Then

  V=±2Delta psi_B(r), y=chi_B(r), r>=0.

The exact supplied T imposes

  V=c(T-1)-R, hence V=-R (mod c).

We show this congruence impossible, for either sign of V and either parity of p.

## Pell residue lemma

For any integer C>=2 and m>=1, write a nonnegative t=qm+j with 0<=j<m. The Pell addition identities and chi_C(m)^2=1 mod psi_C(m) give

  psi_C(t)=chi_C(m)^q psi_C(j) (mod psi_C(m)).

For q even this is psi_C(j). For q odd, the subtraction identity gives

  chi_C(m) psi_C(j)=-psi_C(m-j) (mod psi_C(m)).

Thus every residue is 0 or ±psi_C(j) for 1<=j<m. If m is odd and t is even, the indicated representative index j is even: for q even the original j is even; for q odd, m-j is even.

## Odd main rank p

One has gcd(A,c)=1 because psi_A(p)=±1 mod A for odd p. Also A divides psi_A(j) for every even j. The duplication identity says

  2A psi_B(r)=psi_A(2r).

Applying the parity-refined residue lemma modulo c therefore gives

  V=0 or ±Delta psi_A(j)/A (mod c),
  where 2<=j<=p-1 and j is even.

Every nonzero displayed magnitude is at least 2Delta. Every magnitude is strictly less than c/2. To see the upper bound, monotonicity reduces to j=p-1; writing psi=psi_A(p-1), chi=chi_A(p-1),

  A c=A(A psi+chi)> (A²+Delta)psi >2Delta psi,

because A chi>Delta psi. Hence Delta psi/A<c/2.

But 0<R<Delta<c/2, so -R cannot equal 0 or one of these signed least-absolute residues. This excludes odd p, including r=0.

## Even main rank p=2m

Put b=psi_B(m). Duplication gives c=2A b. Since V is even, the congruence V=-R mod c first forces R even. Divide by 2 and then reduce modulo b:

  ±Delta psi_B(r)=-R/2 (mod b).

By the unrefined residue lemma the left side is 0 or ±Delta psi_B(j), 1<=j<m. Every nonzero magnitude is >=Delta. Every magnitude is <b/2, because

  b=2B psi_B(m-1)-psi_B(m-2)
   >(2B-1)psi_B(m-1)>2Delta psi_B(m-1).

Also c>A Delta² gives b>Delta²/2>R. Thus R/2 lies strictly between 0 and b/2 and is strictly less than Delta. It cannot equal one of the displayed signed least-absolute residues. This excludes even p.

## Conclusion and limitation

The negative auxiliary branch is impossible on every genuine compiler slice. Therefore every full positive83 zero has

  norm_aux=z²>0

for a positive integer z with z²|Delta. The same small-norm descent also gives z|V and z|y, since each positive small-norm solution is an integral iterate of the diagonal seed (z,z).

If Delta is squarefree, norm_aux=1. No claim is made that all other factors are units, that A is even, that p exists on a general candidate zero, or that the ordinary-input language is sound. The p notation in this proof is legitimate only after Na<0 has forced the five other factors to be units.
