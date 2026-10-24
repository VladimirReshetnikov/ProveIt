# Bounded audit of the 98-to-96 expanded-carrier update

This audit concerns only a pointwise polynomial identity. The reviewed 98-operation coprime-fusion ordinary proof remains the mathematical reduction; no new number-theoretic assumption or witness transformation is introduced.

Put d=q(q-1), P=q^4(q-1)=q^3*d and W=1+dL. The former integer carrier is

    Zold=P*mu^2*(H*(n+V)+Kpos)
         +H*(mu^2*(dY-q^3*WB-(q-1)X)-P*e).

Expanding WB=B+dLB, and using q^3*d=P, yields identically

    Znew=P*mu^2*(H*(n+V-LB)+Kpos)
         +H*(mu^2*(dY-q^3*B-(q-1)X)-P*e).

Their difference is H*mu^2*LB*(P-q^3*d), which is the zero polynomial. This holds over the polynomial ring over the integers for arbitrary values, not just positive inputs, valid source witnesses, or sampled controls. No division is used.

The new evaluation shares the already available d=q(q-1) to compute P=q^3*d, deleting the private q^4 multiplication. In the transport carrier, deleting dL, W=1+dL, and WB saves two multiplications and one addition; inserting LB and n+V-LB adds one multiplication and one subtraction. Thus the net update removes two multiplications and one addition and adds one subtraction, taking the count from 98=59+21+18 to 96=57+20+19.

All other kernels, M, the fused radicand and auxiliary radicand remain unchanged. Since Znew=Zold, the full scalar equation N is literally the same polynomial. Hence both positive-zero directions, all sign and integrality arguments, and the exact degree-266 coefficient established for the 98-operation evaluator transfer without further mathematical work. The variables and fixed coefficient tuple are unchanged. The old W remains legitimate proof notation even though its register is no longer evaluated.

The complete inserted/deleted/changed row inventory and universal symbolic carrier identity are additionally verified by the independent portable audit.py. Its unchanged direct-form evaluator deliberately retains W and the original 98-operation mathematical formula, so its signed and positive controls test the new graph against the old formula rather than copying the new implementation.
