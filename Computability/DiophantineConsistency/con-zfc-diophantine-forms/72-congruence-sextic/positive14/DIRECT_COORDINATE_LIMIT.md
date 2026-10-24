# Limit of the direct E-coordinate attempt

The proved fourteen-coordinate construction retains X and Y and adds E=XY.
It is tempting to remove X and supply only E,Y, recovering X=E/Y during
soundness. The original carrier proof does not justify that removal.

For the first carrier, write X=E/Y and keep ell=EkY. Its monic square
equation still formally makes tau=Z/M0 integral. But the polynomial
denominator clearing gives

    YZ=M0 Y(ell+r)+(q-1)Y^2
       -q^3[(qK0Y+E)C-qFY].

The divisibility M0Y | YZ yields only q^3 | Y^2 on reduction modulo q^3.
It does not directly recover the original conclusion q^3 | Y. Thus the
old lower bound Y>=q^3, used to separate index congruences from their
possible integer multiples, cannot be imported into this attempted proof.

The main carrier changes as well. With M=4q^2Y, H=4(E+Y)+3, and
v=k-R-1, its rational root numerator becomes

    Dstar=4q^2E+M ac+H(M gamma+4qE-v).

Monic-root integrality gives

    M | 4q(q+H)E-Hv.

Reduction modulo S=4qY no longer isolates v. Recovering Y|E and recovering
the index would require an additional argument controlling these mixed
congruences. No such argument is asserted here.

These observations identify proof gaps in the direct thirteen-coordinate
substitution; they are not counterexamples to a suitably modified
construction and are not an impossibility theorem. The delivered
fourteen-coordinate lift resolves the issue by its explicit residual
E-XY and exact unique extension of every original positive solution.
