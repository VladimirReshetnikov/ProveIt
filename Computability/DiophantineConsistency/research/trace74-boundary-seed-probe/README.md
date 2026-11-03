# Trace74 arbitrary-port boundary seed probe

This is a **finite partial-constraint probe**, not a positive graph zero and
not a counterexample to the reverse guard. It tests the 74-row candidate at
arbitrary natural ports `beta=1, K0=0, MC=0, MF=0`. With positive candidate
witnesses `J=F=C=1`, `w=7`, `s=1`, `eta=1187`, `zeta=5985`, it obtains

```
q=2, X=14, Y=8, P=X*Y²=896,
k=7172, c=58563, R=3, old alpha=q-F-C=0.
```

The new guard fails at equality `F+C=q`. The first Pell index two equation
holds: `k=2*psi_2(2P+1)` and `E=6429697²`. The main Pell ordinate at index
three also holds: `c=4*(X*Y+Y+1)²-1`, with `0<eta<k`. These checks show that
those **partial** arithmetic constraints alone do not force the new guard at
arbitrary ports.

The other candidate witnesses are merely trial values `i=T=n=1`; the exact
74-row output for this full trial is nonzero, as the script verifies. No
claim is made that changing these witnesses can produce a zero. The ports
also violate the fixed tuple's `0<MC<beta` bound (and `beta=1` is far smaller
than the symbolic fixed beta). Even an eventual all-port counterexample here
would not disprove a fixed-port guard.

Run `python3 -I -S -B check.py`; `observation.txt` captures the result and a
hash of the signed decimal graph output. The script pins the candidate graph,
evaluates every row with exact Python integers, and checks all displayed
identities and nonzero output. It does not invoke Lean or prove unbounded
mathematical claims.
