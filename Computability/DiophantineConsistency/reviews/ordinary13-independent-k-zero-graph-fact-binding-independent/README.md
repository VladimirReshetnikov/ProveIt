# Independent review: independent-k zero-k graph facts

The generated child Lean literal matches all 84 rows, 13 input slots, four port slots and exported field positions of the pinned candidate. In an exact integer-polynomial replay of every relevant row with coordinate 10 set to zero, the first field becomes `Z=b*r-B`, `ell=k=0`, and `A0=Z²-b²`. The actual signed rank is

```
Rring=(alpha+(q-F)*b)*(q²-1)+J*(MC+q*MF).
```

At the same valuation the main root and residual are exactly

```
Dstar=U*(X+a*eta)+H*(U*gamma+Rring+1),
A1=Dstar²-U²*(1+(H+a²)*eta²).
```

Here `q=1+beta*J`, `X=q*w`, `Y=q³*(n_s+1)`, `U=Y*q²`, `a=XY+Y` and `H=3+4a`. The checker verifies these expressions as polynomial identities with all 12 relevant witness/port quantities independent; a dependency check confirms the ignored inputs cannot affect A0 or A1.

The source uses the same `intPorts` and valuation in both calls to the proposed unit bridge and passes the same fixed tuple into `zero_k_fact_cut`. The bridge's signed norm statements and the fixed-client signature match the displayed first and main facts. The final client still explicitly assumes `rankRing v=ι R`; it does not produce R or justify a natural truncated-subtraction representation. Its opposite orientation at the fact-cut call is supplied by `hR.symm`.

This is a bounded source and algebra review. The proposed graph-to-unit proof, casts, `simp`/`convert`/`ring` terms, R representation, the fixed-client proof, provider closure and axiom reports have not been elaborated. Nothing here establishes a graph zero map, an iPRA endpoint or a PDF binding.

The checker reproduces the author's receipt, verifies the generated graph transcript and replays the zero-k fields in an exact multivariate polynomial ring. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B reviews/ordinary13-independent-k-zero-graph-fact-binding-independent/check.py | cmp - reviews/ordinary13-independent-k-zero-graph-fact-binding-independent/receipt.json
```
