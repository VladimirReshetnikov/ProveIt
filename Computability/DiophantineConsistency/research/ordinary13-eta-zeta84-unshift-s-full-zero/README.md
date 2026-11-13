# Full compact-port zeros after removing s's shift from the eta/zeta 85 probe

Deleting `s=n_s+1` from the pinned [eta/zeta-natural 85-row probe](../ordinary13-eta85-zeta-zero-boundary-audit/probe.json) and replacing its use by `n_s` gives this 84-row graph. It has full nonnegative-input zeros with `n_s=0` for every natural port tuple with `beta≥2`, including `Residue90CompactPortBoundsDraft.ports K` for every natural K. Thus the altered graph does **not** force s positive at those compact ports. This does not settle whether some different witness map relates its zero existence to the parent, or provide a consistency equivalence or iPRA proof.

For arbitrary integers `beta≥2` and `K0,MC,MF≥0`, define

```
h = ceil((K0+2)/beta)
w = beta*h-K0-1
q = beta+1
R = (1+beta²)*(q²-1)+MC+q*MF
k = R+1
t = (beta-1)*(w+h)-1
B = beta*t
r = k*(B-1)+t+1.
```

The ceiling ensures `1≤w≤beta` and `h≥1`; hence `t≥1`, `B≥2`, `R≥1` and `r≥1`. In the 84-row input order use

```
(n_J,n_F,n_alpha,n_f,n_i,n_T,n_w,n_s,n_r,n_eta,n_zeta,n_y,n_gamma)
= (1,0,0,2,2,R-1,w,0,r,1,R,1,0).
```

The graph then has `Y=U=E=ell=0`, `c=1`, `a=0`, `H=Delta=3`, `k=R+1`, `Bt=B`, `Z=beta`, `Dstar=0`, `Q=9`, `I=3` and `V=-1`. Its first and main residuals and strong residual are zero, and its auxiliary factor is one; consequently its complete output is zero. The compact beta is `2^(67*8807)-1`, and the other compact ports are natural, so the hypotheses hold without expanding those fixed integers.

The checker builds the precise 84-row graph from the pinned parent and evaluates **every** row as an exact polynomial in `beta,w,h,MC,MF`, with `K0=beta*h-w-1` and the displayed witnesses. It verifies the four factor residuals and final zero symbolically. A small separate exact-integer control uses ports `(2,0,1,1)` and evaluates the parent as nonzero at the same tuple; that same-tuple observation does not establish anything about other parent zeros. No huge Pell integer is computed.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-eta-zeta84-unshift-s-full-zero/check.py | cmp - research/ordinary13-eta-zeta84-unshift-s-full-zero/receipt.json
```

This is an external exact-integer construction; the original probe's own zero equivalence, a model-level construction, compiled providers and an iPRA endpoint remain unproved.
