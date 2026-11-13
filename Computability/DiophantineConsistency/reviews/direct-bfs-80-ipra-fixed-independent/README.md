# Independent review: fixed symbolic direct-BFS 80 iPRA client

The accepted `DirectBFS80FixedIPRA.lean` provides four **assumption-free Lean theorem declarations** constructing derivability terms for a fixed symbolic port tuple. The exact tuple is

```
ports betaNat (DirectBFSSymbolicKernel.paramKernel rho) lowNat highNat
```

and its fourth component is `betaNat+highNat`, as proved by the generic `port_three` projection. The other projections give beta, the **directly indexed BFS symbolic kernel**, and the low mask. The four hypotheses of the reviewed parameterized client are discharged by these generic `rfl` projections; no port premise remains in the four endpoint statements.

All four left sides use `IPRAExpressionNative.nativeNoZero (positiveShift (graph (integerPorts fixedPorts)).output)`, with the positive shift applied **once**. The `standardTheory` endpoints have respectively `∼mappedNativeRefutation embedding` and `(Semiformula.lMap embedding sourceSentence)ᴺ` on the right. The equality-only `referenceTheory` endpoints use `erase` on the no-zero term and respectively `∼erase (mappedNativeRefutation embedding)` and `erase ((Semiformula.lMap embedding sourceSentence)ᴺ)` on the right. These are Lean proofs that the encoded equivalences are derivable in the named theories; they do not prove the consistency sentence true.

`check.py` rehashes source/copies, runner, Lean binary, the direct provider, output and logs; verifies equal before/after pins and first direct resolution; checks 59 retained chunk receipt hashes; and compares the selected common 80 graph and BFS symbolic-kernel objects with the previously audited client chain. The direct `DirectBFS80IPRA` object is `5a568d6580ca19a563a5e59514adcaffea499691183734df13bee9d27d2e4082`; this fixed output is `2155f5f05a8e993dc3582f3c14ce9c56916d0ac09dc326c02093d83a878e4703`. Exact paths and hashes are in `check-output.txt`.

All four captured named axiom reports are exactly `[propext, Classical.choice, Quot.sound]`, with empty inner stderr; the runner enforces the named whitelist and rejects coded diagnostics. The separate supervisor's terminal records **runner subprocess exit 0**, matching before/after source, runner and supervisor hashes, and outer log hashes; its retained stdout contains the matching inner result and exact reports. The supervisor writes its receipt before its own final assertion; the author observed its successful outer process exit, but that supervisor exit is not separately self-certified by the receipt. No independent Lean replay was performed.

The full serialized transitive closure and historical source-object, package-transitive and dynamic ancestry remain inherited. The external retained gzip/JSON-to-Lean symbolic-kernel binding has separate finite byte/recipe evidence but is not an internal Lean equality in this packet. This is the direct-BFS symbolic K, not the distinct original-order symbolic K, the trace75 graph, or the original 14-variable PDF.
