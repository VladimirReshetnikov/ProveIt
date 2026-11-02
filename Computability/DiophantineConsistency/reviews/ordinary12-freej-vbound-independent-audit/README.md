# Independent bounded replay of free-J graph V bound

The source in commit `e3019d81e5` was independently recompiled in a fresh
temporary overlay using its pinned historical early-size parent. The actual
replay process exited 0 in tool session 45686 and printed
`PASS_BOUNDED_FREEJ_GRAPH_V_BOUND` with receipt SHA-256
`12211b01bcf357087a91d90e11872e196cf35f39d2eb7cb9198efdaffe2f5d2f`.
The exact receipt is retained here, including the compiler command, five
axiom reports, direct dependencies, object hash, and 83 checked historical
inputs. The replay ran with Python `-I -S`; it did not rebuild its parent
closure or the package provider.

The main Lean theorem concerns an `IΣ₁` model, not an object-level iPRA
derivation. It assumes twelve positive coordinates forming an internal zero
of `Ordinary12FreeJ.literal` and natural ports satisfying `p₀>0`, `p₂<p₀`,
and `p₃<2p₀`. Its signed-pair conclusion is `1<c` and `z.2+c<z.1`, where
`z` evaluates the displayed graph expression `V`. The theorem uses the
historical early-size and first-factor transports to obtain `2R<c` and the
bound on `F`, before the strong norm. The `shape` theorem binds the expression
inside the Lean core's ordinary tail; the separate previously reviewed
95-row source checker connects that Lean core to the manuscript JSON. It is
not a Lean theorem directly interpreting a JSON file.

For the elementary bound, positive `T,t` give `Tc>=c` and `(1+t)²>=4`.
From `2R<c`, the difference `u=Tc-R` is positive and `R<u`; hence
`2c<=2(u+R)<4u<=(1+t)²u`. The example `c=3,R=2,T=t=1` shows that the
premise `2R<c` cannot simply be dropped. Signed graph evaluation of `q-F`
is identified with natural truncated subtraction only after proving `F<q`;
the graph-to-model distinction is material.

The replay uses previously compiled historical objects and package/provider
artifacts. It is not a matched full-project source-current replay, a complete
package-transitive or dynamic dependency audit, a proof that the actual
compact44 tuple meets all application and checker-calibration requirements,
or a proof in iPRA. The nonzero denominator, integrality descent, remaining
witness reconstruction and both consistency directions remain separate.
