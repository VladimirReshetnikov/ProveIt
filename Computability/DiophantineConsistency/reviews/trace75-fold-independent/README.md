# Independent review: trace75 noncircular odd-ordinate recovery

The frozen accepted packet establishes the conditional model-level recovery stated in `FOLD.md`. `check.py` rehashes source/copies, runner, recorded pinned inputs, Lean executable, output object and logs, and checks first-resolved direct and selected inherited providers. It verifies the three Pell modules are selected from the fresh generic rebuild; exact paths and hashes are in `check-output.txt`. We did not replay Lean or audit the complete transitive/package/dynamic provenance.

For an `ORingStructure V` model of IΣ₁, `Trace75Fold.graph_odd_ordinate` assumes arbitrary natural ports `p` with `0 < (p 0 : V)`, all ten coordinates of one `v` positive, and zero of Lean's trace75 `value75` at the same port casts and embedded tuple in `DiffRing V`. It concludes one `r,j,I : V` with `0<r<j`, `r%2=1`, `0<j`, `0<I`, and

```
c p v = ycoord r (A p v−1)
xcoord j (A p v−1) = 1+2*(delta p v*U p v*U p v*E p v)
ycoord j (A p v−1) = I
(c p v)² ∣ I.
```

The chart is explicitly `A−1`, where the Lean `A` abbreviation is `X*Y+Y`; it is not an unqualified assertion using a differently normalized base. The intermediate `signed_coordinate` takes the same joined witnesses `I,j,h`, combines the two signed residues through their **same** `V0` and obtains `SignMod F c (ycoord (2*h+1) (A−1))`. Positivity and divisibility give `c<I`; positivity of the original coordinates yields `delta≥4`. The ordinary Pell norm for the already-classified strong index then gives `2*I<F`. These are exactly the size and signed-congruence inputs needed by the generic `recover_odd_ordinate` at `n=j`, `s=2*h+1`, `b=A−1`, and `c=c p v`. It does not assume the desired final target main norm, exact rank/index equality, or an 80-graph zero; it does use the ordinary Pell norm of the derived strong coordinate. The statement is a necessary consequence of a positive trace75 zero, not a converse, machine halt bridge, trace74 guard, iPRA theorem or Lean JSON/constant-byte binding.

The direct `PellRecovery` selects `/tmp/pell-generic-fold-1n_2g52k/PellRecovery.olean`, hash `0deec819d3d49c3ebfe8179175613095e6497272cfc6cc1d7723c8df6b32524a`; selected `PellOddFold` and `PellFold` also come from that fresh generic root. The audited generic rebuild removed the earlier **direct** `Direct80Joined` import, but its runner did not separately rehash earlier-stage output around later imports; a complete transitive exclusion of old graph modules is not claimed. Direct `Trace75Joined` is the audited object `be92565d27f2893ed85e46c44d726a7a699d51ee9019105f932446831be7b305`.

The accepted output object is `60d26b62219b41539aecf950465beee7e90df5a50f78e14ac8670d47c2ef5263`, with recorded inner Lean exit 0, exactly `[propext, Classical.choice, Quot.sound]` in its named report, and empty stderr. Attempt01 failed to resolve the historical direct 80 import and attempt02 failed elaboration; neither is the accepted artifact. The runner checks coded warnings/errors and `sorryAx` but not a named axiom whitelist; the report was inspected independently. The terminal precedes final runner assertions and no separate actual outer-exit receipt was found.
