# Complete accounting for two shifts of the main Pell root

This records a bounded search around the frozen 102-operation circuit.
It is independent of the later successful doubled-index change.
`explore_round22_shifted_main_root.py` builds six complete schedules
and checks every transformed source residual and triangular correction.
All counts treat numerals as free.

Write A=a+4, D=A^2-1 and M=8a+15. In the existing certificate,

    d=U+a*c+gamma*M,
    d^2=D*c^2+1,
    I=of-d

are used by the main exponential equation, main norm and signed norm.
The other uses of c, D and c^2 are retained in all counts.

| Supplied coordinate | Main norm treatment | Signed root treatment | Complete count |
| --- | --- | --- | ---: |
| eps=d-a*c | Reconstruct d | of-d | 102 |
| eps=d-a*c | eps*(eps+2ac)=M*c^2+1 | Reconstruct d | 104 |
| eps=d-a*c | Same factored norm | of-eps-ac directly | 104 |
| eps=d-(A-1)c | Reconstruct d | of-d | 104 |
| eps=d-(A-1)c | eps*(eps+2(A-1)c)=2(A-1)c^2+1 | Reconstruct d | 106 |
| eps=d-(A-1)c | Same factored norm | of-eps-(A-1)c directly | 106 |

These coordinate changes preserve positive domains. In the first case
eps=U+gamma*M>0. In the second case the main norm gives

    d^2-((A-1)c)^2=2(A-1)c^2+1>0,

so d>(A-1)c. Conversely either positive eps reconstructs a positive d.
The signed root itself remains an unrestricted integer register, just
as in the frozen certificate.

For eps=d-ac, shortening the exponential equation saves two
instructions, exactly the product ac and addition eps+ac needed to
reconstruct d. Factoring the norm costs two further operations after
that reconstruction has been counted. Expressing the signed root
directly simply replaces one reconstruction addition by an additional
subtraction.

For eps=d-(A-1)c, the exponential equation is
eps+3c=U+gamma*M. The product 3c and addition on its left offset the
local benefit, while reconstruction of d still costs two instructions.
The existing c^2 register cannot be dropped: E16 uses it independently
of the main norm.

The checked histograms are 56 multiplications and 46 additions at 102;
57 multiplications and 47 additions at 104; and 58 multiplications and
48 additions at 106. Each complete schedule retains 34 positive
unknowns and 22 equalities. These are exact obstacles for the displayed
constructions, not arithmetic-circuit lower bounds.
