# Independent review: seven forced inputs in the AQ17 natural graph

This is an external, all-model mathematical review of the 17-variable, 104-operation natural candidate. Run `python3 -I -S -B check.py` from any directory and compare with `result.json`. The author's receipt also reproduces. No Lean, staging, provider audit or internal iPRA proof was performed.

The checker independently expands the parent under exactly the mixed substitution and the complete child: all 9,875 integer polynomial terms and all eight named residuals agree for arbitrary integer inputs and ports. All rows, inputs and ports are live and the output is exactly eight residual squares. Its port-independent monomial `n_Y⁸*n_eta⁸*n_i⁴` has coefficient 1, proving exact degree 20 for every fixed integer port tuple. The mixed-substitution equality is pointwise; the fully shifted graph is generally a different polynomial at the same natural tuple.

The first six unshifted inputs are forced positive independently of every port, exactly as detailed and checked in the [17/105 independent review](../adaptive-aq17-natural-forced105-independent/README.md): the two norm equations force the quotient inputs positive; the strong and auxiliary residuals force `vValueVariable`, `f`, and `y` positive; the v-binding residual forces `T` positive. All arguments remain valid simultaneously with `J` unshifted, because they depend only on the ten remaining shifted inputs and on other unshifted inputs being nonnegative.

The seventh input `J` needs a separate port condition. The checker independently expands the exact parent first-root binding at `J=0` and obtains

```
zDifference = Bt = (1 - F - alpha)*(X + K0) - F.
```

The shifted `F,alpha,X` are positive model naturals. If the second port `K0` is represented by a model natural, then `X+K0>0` and `1-F-alpha≤-1`, so `Bt<0`, contradicting the zero residual. This argument uses no positivity of the other six unshifted inputs. It cannot be generalized merely to arbitrary signed `K0`: for `F=alpha=X=1` and `K0=-2`, this displayed `Bt` is zero. The pinned source `ModelThirteenCarrier.port1` identifies the selected second port with the difference-ring image of `CurrentKernel2011.K : V`, and the pinned kernel source defines K as a natural. Their compiled providers and application to this new graph have not been authenticated.

For the fixed represented nonnegative second port, the seven forced-positive arguments yield a positive parent zero; conversely a positive parent zero gives a child zero by taking predecessors only for the ten shifted coordinates. This is an external zero-existence argument in ordered IΣ₁ models using the difference-ring order, discreteness and the sum-of-squares property. The earlier AQ20 bridge separately requires positive represented beta. No Lean client, literal iPRA proof, current provider closure, formal PDF semantics or global minimum is established.
