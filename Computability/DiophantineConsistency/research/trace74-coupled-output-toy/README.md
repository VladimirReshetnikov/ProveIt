# A fully evaluated abstract coupled-output example

This deliberately small example checks the Pell-orbit and carrier algebra
with concrete integers. It is **not a witness for the 74 graph**: its
registers are selected independently and do not satisfy all graph input
definitions or the fixed symbolic coefficients.

The diagnostic takes `lambda=2`, `Delta=3`, `c=tau=i=1`, yielding
`a=3`, `F0=4`, `freg=7`, `S=12`, and `Q=S²=144`. The odd auxiliary index
5 gives `V=328901`, `y=330049`, satisfying
`Q*V²−(Q−1)*y²=1`. With signed rank `R=−1`, the actual register shape
`V=freg(cT−R)−c` is satisfied by the positive integer `T=46985`.

For independent abstract carrier registers `h=D=H=Breg=M=1`, `e=2`,
`Kreg=3`, the constant `N0` is zero and
`v7=V² Breg−N0+tau*sqrt(F0)*y` is positive. The actual carrier expression
then gives `Z=M*tau*sqrt(F0)*y`, and substituting these numbers into
`Q(Z²−M²(E F0)V²)+(M²(E F0)−Z²)` gives exactly zero. These register
choices are an algebra exercise; the example does not bind them to one
trace74 input tuple.

Run from the repository root:

```text
python3 -I -S -B Computability/DiophantineConsistency/research/trace74-coupled-output-toy/check.py
```

The checker is finite, external, fail-closed under Python optimization,
and does not establish the huge symbolic-beta witness or any iPRA claim.
