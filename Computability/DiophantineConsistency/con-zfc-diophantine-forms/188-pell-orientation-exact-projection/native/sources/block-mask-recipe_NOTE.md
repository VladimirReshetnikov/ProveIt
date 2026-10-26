# A block mask and an inline weighted polynomial

This is an exact recipe identity for the complete low-padding2963 tuple.
All four fixed integers, the entire specialized P66 polynomial and its
positive zero set stay identical. It introduces no new witness-map,
controller or foundational premise.

The full physical support is exactly

    {0..950} union {960..985} union {1005}.

Selectors0..941 meet south labels942..950 to form the first block.
North960..968, west969..976, dummy977 and east978..985 form the second.
The marker1005 remains a separate physical position even though its
weighted coefficient is zero. Consequently the first mask is

    MC=beta-G951(rho)-rho^960*G26(rho)-rho^1005.

The audit proves the formal polynomial identity

    G942(x)+Psi_old(x,1)+x^977
      =G951(x)+x^960*G26(x)+x^1005

on every one of3297 coefficients, including all zeros. This is stronger
than checking just one large numerical evaluation.

The weighted specialization has the independent formal identity

    Psi_old(x,2)=x^969*(x^9+2^17)*G8(2x)
                +2^8*x^942*(x^18+2^17)*G9(2x).

Its old marker term vanishes at2. After the first mask stops using Psi,
the remaining specialization can be inserted directly into Phi:

    Phi(x)=sum_(i=0)^941 [1+2^10*(1+w_i+2^8*n_i+2^17*p_i+2^25*s_i)]*x^i
           +2^10*x^969*(x^9+2^17)*G8(2x)
           +2^18*x^942*(x^18+2^17)*G9(2x).

Here p_i is exactly the existing printed table's east-color name. Every
selector is rebuilt from the complete authenticated942-tile list and all
3297 Phi coefficients are compared with the frozen parent. The physical
polynomial is checked separately; it is never inferred by dropping zero
weighted coefficients.

Both actual corrupted printed MC variants are also evaluated. Omitting
the separate marker subtractand changes MC by rho^1005 and forbids the
marker. Replacing the second block by the split17+8 blocks that skip977
changes MC by rho^977 and forbids the Boolean dummy. Each changes the MC
population from d-978 to d-977 while Phi remains entirely unchanged.
These controls check complete mask values and their actual origin shifts.

The frozen parent page is authenticated byte-for-byte. Its exact MC and
Phi/Psi blocks are replaced once, preserving all other bytes and the
complete tile table. The inline version removes Psi entirely and changes
the complete TeX source from4996 to4970 bytes, saving26. The alternative
univariate Psi helper saves11 bytes over the same exact blocks. The
generated `inline-equation.tex` is the deterministic complete projected
source; these metrics make no claim about a rendered PDF. ROOT handles
the separate candidate build and visual review.

The four complete constant ports remain69,685 unsigned big-endian bytes.
Their hashes, the formal coefficient-array hashes, the literal before/
after blocks and both corrupt-mask controls are in `CERTIFICATE.json`.
The ordinary low-padding proof applies immediately because the whole
integer tuple is equal, rather than merely sharing a necessary condition.

Run `python audit.py` and `python -O audit.py` to reproduce the exact
certificate and projected source; `--write` regenerates both. Every
guard remains active under optimization. All accepted files are unchanged.
