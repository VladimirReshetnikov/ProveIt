# A counterexample to dropping one residual square

The checked 94-operation candidate ends in `A0² + A1² + N²`. A tempting
93-operation tail is `A0² + A1² + N`. These expressions do **not** have the
same zeros for arbitrary natural-valued witnesses and positive integer ports.

In the candidate graph's witness order `(J,F,alpha,t,T,X,Y,r,eta,zeta,n,gamma)`,
choose `(0,0,1,1,1,0,0,1,1,4,2,1)`; choose the four ports
`(beta,K0,MC,MF) = (1,1,1,1)`. Direct evaluation gives

```
A0 = 0,  A1 = 144,  N = -20736,
A0² + A1² + N  = 0,
A0² + A1² + N² = 430002432.
```

Run `python3 -I -S -B check.py` from this directory, or pass its path to
Python from any directory. The script hashes and evaluates the pinned
`candidate.json` using arbitrary-precision integer arithmetic. This is an
external finite check, not a Lean theorem. Its witnesses include zeros and its
ports are not the enormous fixed ports in the displayed candidate, so it
does not rule out a proof under stronger strictly-positive-witness and
specific-port assumptions. It does rule out a same-valuation, all-port,
all-natural-model theorem of the form currently available for the 94-gate
square tail, and it shows why nonnegativity of `N` cannot be assumed generally.

The separate identity `h = (V+n)² - 1 - Q*n*(2*V+n)` also does not by itself
save a gate in this graph: `Q*V² - 1` is used independently in the correction
term. Neither observation is a global lower bound on equation size.
