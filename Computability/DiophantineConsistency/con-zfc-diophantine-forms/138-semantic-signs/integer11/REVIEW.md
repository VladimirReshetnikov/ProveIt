# Independent mathematical review of the 107/108-operation composition

Reviewed within this AI-assisted research workflow on 24 October 2026.
This is a separately performed mathematical check, not external human
peer review and not a newly completed proof-assistant verification.

## Disposition

The composition in `PROOF.md` is mathematically compatible with the
retained package-132 main-root saturation proof and package-131 parity
guard proof. I found no gap in the new compatibility or completeness
argument. The finalizer change is a polynomial identity, so it changes
the evaluation circuit without changing the zero set of the revised
guard polynomial.

## Checks performed

1. The authenticated affine front has q even and both cone coefficients
   divisible by sixteen. Expanding Budget+(qk)^2 gives the displayed
   expression, every summand divisible by sixteen. Therefore Budget is
   0 or 12 modulo sixteen and D=Budget-4 is 12 or 8. These residues exclude
   every integer square, even before a sign is known.

2. With ell=XY^2, ell(ell+1)>=0 for every integer ell, so Dt>=1. Since X
   is divisible by eight, Dt=1 modulo eight. Dg=1+D Dt s^2 and P=Dt Dg
   are 1 modulo four and cannot vanish. This preserves the unconditional
   nonvanishing prerequisites used by package 132's coprime-product
   argument.

3. Substituting the revised P does not alter any of the pairwise gcd
   identities. In particular Df=1 modulo BP, Da=1 modulo BP, and modulo
   Df one has Q=-Delta, delta=-A^2, V=-c, Cy=-Dm, Da=A^2 Dm. Since
   A divides U and Dm divides BP, gcd(Df,A Dm)=1. No sign premise enters
   these reductions.

4. The order of sign recovery is valid. The rational square identity
   first gives absolute squares of BP,Df,Da. Df=1 modulo four forces
   Df>0. If c is nonzero, then U is nonzero because S!=0 already gives
   r!=0; BP<0 would contradict Df>0. The c=0 case is checked separately:
   Dm=Df=Da=1 and the same square identity forces P=BP>0. Thus no argument
   prematurely assumes c!=0 or P>0.

5. With P>0 and Dt>0, Dg>0. If Budget<=3, D<=-1 and s!=0 imply
   Dg<=1-Dt<=0. Hence Budget>=4, sharpened to >=12 by the residue
   computation. This is more than the strict positivity required by
   the centered budget and by the early main-root folding argument.

6. The strong and auxiliary norms used to recover Dm are restored before
   P is split. I=U p0 has c^2|I and |I|>=|c| after c!=0. The folding
   proof cited from the retained package-132 text uses only those norms
   and this bound, not the still-unextracted first-Pell root. Therefore
   extracting Dm=d^2 and then P=(p0/d)^2 does not create a circle.

7. In completeness, the canonical parent values have Dt=tau^2 and
   Budget>64. Thus D>0 is nonsquare, and D Dt is a positive nonsquare.
   Classical Pell existence supplies the required unrestricted positive
   s. The later finite-period strong-pair construction works for this
   new s and p0 without requiring the removed factor four. Its prescribed
   divisibility 4s A p0 c^2|I still supplies the same support for the
   interpolation modulus p0 s r. The ordering of these choices is
   unchanged and noncircular.

8. Direct expansion verifies

       Q(Z^2-RG V^2)+(RG-Z^2)
         =(Q-1)Z^2-RG(QV^2-1).

   The new guard replaces the old highest-degree coefficient by 1/12
   of its value, not by zero; the degree argument is therefore consistent
   with the retained 924 and 840 values. Exact operation counts and the
   authenticated full leading coefficients are the separate executable
   verifier's scope.

## Scope

I read the new proof, the complete `PARENT132_PROOF.md`, and package 131's
`scalar/PROOF.md` in the pinned repository. I checked the changed formulas,
all sign-sensitive cases above, and their composition with the explicitly
stated inherited interfaces. I did not rebuild the full transitive native
compiler or a Lean/Rocq development. The new result remains the ordinary
calibrated equivalence described by the manuscript, not a proof of
Con(ZFC) or a claim of worldwide minimality.
