# A complete ten-positive equation: 98 operations, degree 360

`equation.pdf` and its standalone `equation.tex` print the entire equation
and every fixed constant on one Letter page in 9-point body type. Its ten
unknowns are strictly positive integers J,F,alpha,i,T,w,Y,n,eta,zeta. Every
other symbol is a polynomial abbreviation or a completely specified fixed
integer. The evaluator has 58 multiplications, 22 additions and 18
subtractions. No expanded coefficient table or external program is needed
to interpret the page.

The [ordinary proof](../../research/ten-positive-index-weight/PROOF.md)
changes the transport majorant from `HI+b` to `kI+b`. Before transport,
the unchanged Pell kernels imply `k>H`; thus every required transport
inequality survives. After the old equation has supplied a zero, the
positive integer map `n_new=n_old+(k-H)*I*Bt` preserves its full center.
The independent soundness proof uses the new weight throughout. This is
existence equivalence, with no asserted positive inverse map on every zero.

The page also incorporates the accepted zero-offset base and the exact
expanded-transport identity. Compared with the preserved
[101-operation, degree-368 page](../one-page-short10/equation.pdf), it saves
three operations and lowers exact degree by eight. The distinct direct-base
103-operation, degree-332 equation remains a separate tradeoff.

The exact degree follows from the centered octic: its highest homogeneous
part is

    2^20*(beta*J)^184*w^36*i^20*Y^76*(eta+zeta)^40*(beta*J-F)^4.

The selected coefficient at J^184*w^36*i^20*Y^76*eta^40*F^4 is
`2^20*beta^184>0`. The other three fixed ports do not enter it.
This applies to the complete coherent BFS tuple printed here.

The entire fixed-constant body is verbatim from `one-page-short10`,
including all 436 seed characters, the ordered 62-symbol alphabet, the
closed transition decoder, all 943 tiles, arithmetic ranks and all four
coefficient recipes. Original and BFS native K values are distinct; no
port is interchanged individually. The whole state/color/native/controller
transfer is inherited from that preserved page. The renderer matches every
printed arithmetic definition to the entire 98-gate graph symbolically
over four free coefficient ports. The tuple checker reconstructs every
coefficient byte and checks the full native and conjugacy data.

These ordinary arguments give the same ZFC-provable equivalence between
absence of positive zeros and syntactic Con(ZFC). Lean remains paused;
this page adds no internal object-ZFC theorem or assertion of consistency.
The complete parent, renderer, proofs, constant body and replay records
are content-pinned in SOURCE_PINS.json and the closed manifest.

Reproduce from the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/render_index_weight10_page.py --render
python -B Computability/DiophantineConsistency/tools/verify_one_page_tuple44.py --output Computability/DiophantineConsistency/candidates/one-page-index-weight10
```

Repeat both commands with `-O` for the optimized-mode records. The root
review and final seal record the actual validation and promotion status.
