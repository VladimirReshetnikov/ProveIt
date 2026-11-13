# Scalar obstruction to deriving the trace74 guard from saturation alone

An exact finite assignment satisfies the four-block equation, all its scalar saturation hypotheses, and both resulting no-carry conditions while violating the desired guard:

```
d=5, beta=31, q=32, J=1, MC=14, HP=12, MF=beta+HP=43
F=16, C=17, M=MC*J+1=15, H=HP*J-1=11, R=507775
```

Here `q=2^d=beta*J+1`, `0<MC<beta<MF<2*beta`, `MC` is even, `HP mod 8=4`, and `pop(MC)+pop(HP)=5`. Both `C-1` and `F` are below `q`, `M<q`, and `HP*J>=1`. The exact four-block identity holds, `pop(M)+pop(H)=7=d+2`, and `pop(R)=17=3*d+2`. The pairs `(C-1,M)=(16,15)` and `(F,H)=(16,11)` have disjoint binary bits. Nevertheless `F+C=33>q` and `F>MC*J=14`. Thus even deriving both no-carry statements from the saturation hypotheses would not by itself yield the desired guard or the additional comparison `F<=MC*J`.

For extra context, the selected candidate's integer `R` cone gives the same number and satisfies `3*q<R`, `R+q^3+q+1<q^4`, and `R mod 4=3`. With `eta=zeta=1`, `s=R+1`, its `c` cone gives `c=33277607937>2*R`. The script evaluates only these two cones, leaving `K0`, `i`, `T`, `w` and `n` unspecified. These **are not the fixed BFS ports**; the example is not a positive zero of the full graph and does not refute a fixed-port guard or 74/75 equivalence. It shows which scalar argument needs an additional graph or fixed-mask-specific premise.

`check.py` pins the candidate JSON, evaluates the exact integer cones and checks all stated inequalities using Python integer arithmetic. Its captured `stdout.json` is not a Lean theorem. `ScalarObstruction.lean` is an **unchecked** finite binary arithmetic draft; its 20-bit functions are separate from the internal model population and no-carry definitions. It does not bind the JSON or assert a graph zero.

Run `python3 -I -S -B Computability/DiophantineConsistency/research/trace74-saturation-scalar-obstruction/check.py` from the repository root. The author tool exited 0. Checker SHA-256 `3526e97357dc75bf812bb33265eadcbb670967c3989037b50e19403427fd0b84`; stdout SHA-256 `a97e88fc1e5d4bb5666c23cc677dab8f38e7400d263e6a8de4107596c9d2777e`. The inner terminal does not independently capture outer tool exit. Independent audit: [`reviews/trace74-saturation-scalar-obstruction-independent/README.md`](../../reviews/trace74-saturation-scalar-obstruction-independent/README.md), SHA-256 `c07cf6626fe87846d888d9354bb29b0c1c12a09d434c1bc71339f55c9e650bdb`. It checks only the external finite scalar statement, not a Lean replay or internal model predicates.
