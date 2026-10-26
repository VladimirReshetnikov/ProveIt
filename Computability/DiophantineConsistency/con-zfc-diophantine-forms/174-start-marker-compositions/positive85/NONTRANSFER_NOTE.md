# Why the trace-linear substitution does not automatically apply to P66

The new ten-positive construction has the literal identity f=1+2a with
a divisible by c^4. Thus f=1 modulo c before any equation is imposed.
The maintained fifteen-positive P66 construction instead treats f as an
independent Pell root and proves only f^2=1 modulo c. It is invalid to
replace f^2 by f there solely by citing package 163.

This is a structural obstruction, not a counterexample to the complete P66
consistency theorem. Let A>=2 and let R>=3 be odd. Write
c=psi_A(R), D=chi_A(R) for the usual Pell ordinate and trace.
Then c is odd, D^2=1 modulo c, and strong divisibility together with the
Pell multiplication formula gives

    c^2 divides psi_A(cR),
    chi_A(cR)=D^c=D modulo c.

Indeed psi_A(cR)/c = c D^(c-1) modulo c. Since c is odd and D^2=1 modulo c,
the trace congruence follows. Put f=chi_A(cR) and i=psi_A(cR)/c^2.
Then f,i are positive integers and

    f^2-(A^2-1)i^2c^4=1,

exactly the normalized strong norm. Nevertheless

    D=A c-psi_A(R-1)
      = c-psi_A(R-1) modulo c

is neither +1 nor -1 modulo c: 1<psi_A(R-1)<c-1.
For example A=2,R=3 gives c=15 and f=11 modulo15.

Hence V=f(cT-R)-c would have residue -fR modulo c, whereas the old
V=f^2(cT-R)-c has the required residue -R. A new soundness argument would
have to handle that genuine difference; canonical completeness alone cannot
remove it. No endpoint based on that unproved shortcut is supplied.

