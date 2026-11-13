# Independent review: trace75 strong and auxiliary Pell indices

The frozen source, runner and accepted receipt support the conditional joined theorem described below. `check.py` rehashes the source/copies, runner, Lean executable, all recorded input pins, object and logs, and resolves direct and selected support objects through the recorded search path. Exact paths, hashes and direct/inherited labels are in `check-output.txt`. We did not replay Lean or audit the full project/package/dynamic producer ancestry.

For any `ORingStructure V` model of IΣ₁, `Trace75Joined.strong_and_auxiliary_indices_with_graph_residue` assumes arbitrary natural ports `p` with `0 < (p 0 : V)`, an all-positive tuple `v : Fin 10 → V`, and zero of the actual Lean `value75` at the same embedded tuple and port casts in `DiffRing V`. With the previously bound expressions `D=delta p v`, `U0=U p v`, `E0=E p v`, `A0=A p v`, `a=D*U0*U0*E0` and `F=1+2*a`, it supplies **one** tuple `tau,f,V0,y,I,j,h` satisfying:

* `tau,f,V0,y,I,j > 0` (no positivity of `h` is claimed), `E0=tau²`, `1+a=f²`, `I=2*U0*tau*f`, and `(c p v)² ∣ I`;
* the strong solution `xcoord j (A0−1)=F` and `ycoord j (A0−1)=I`;
* the odd auxiliary solution `xcoord (2*h+1) (D*I−2)=(D*I)*V0` and `ycoord (2*h+1) (D*I−2)=y`;
* `SignMod F V0 (c p v)` and `SignMod F V0 (ycoord (2*h+1) (A0−1))`, with `SignMod` meaning equality or additive inverse modulo `F`.

The proof obtains the common `tau,f,V0,Z0,y` from the audited adjacent theorem, then constructs `I`, `j` and the odd index `h`. The proof uses the **same** `V0` from the square representative for both residue claims; `Z0` is an internal witness used in the derivation and is not quantified in the final conclusion. It proves the natural subtraction bounds needed for `A0−1` and `D*I−2`. Its first signed residue uses the audited trace75 single-factor unsquared register; the second uses the strong Pell norm and odd quotient transfer. No all-index folding, equality of the two ordinate terms, `c`-is-Pell-ordinate result, trace74 guard, machine halt equivalence, iPRA theorem or external JSON/constant binding follows here.

The accepted object is `be92565d27f2893ed85e46c44d726a7a699d51ee9019105f932446831be7b305`. Its direct imports first resolve to the previously audited `Trace75Residue` `205d69b70c084f2613a94f465f3b46fd59f142f755e34897dd4257b16c819e8d`, `Trace75Adjacent` `f8b22b6107778dd98a51e6aa356d8190a0be377c811bceeff43dfcd1b19f17ea`, and pinned `ArithmeticPellHalfIndex`. Other selected trace/root and adjacent providers match recorded inputs; observed first paths are post-hoc evidence, not proof of the whole compile-time closure.

The retained receipt has inner Lean exit 0; the only axiom report is exactly `[propext, Classical.choice, Quot.sound]`, formatted over multiple lines, and stderr is empty. The runner rejects coded warnings/errors and `sorryAx` but does not enforce an explicit named axiom whitelist; the report was checked separately. The terminal is emitted before the final guard; no separately retained actual outer-exit receipt was found.
