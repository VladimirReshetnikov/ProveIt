# Compact tuple, retained bytes and the residue-90 model ports

The residue-90 source already has the right **symbolic** port shape. Its `Residue90CompactPortBoundsDraft.ports K` is the natural tuple

```text
[CompactFixedBeta.betaNat, K, CompactSymbolicPorts.lowNat,
 CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat].
```

`CompactSymbolicModelIff.p` uses the same four terms cast to integers, with the particular choice `K=CompactSymbolicKernelOpaque.paramKernel CompactSymbolicKernel.rho`; `rho=2^67`. Thus selecting that K and proving the componentwise natural-to-integer tuple equality is the direct source-level join. The draft's arbitrary K is **not** itself a proof that it is that particular kernel. The fourth port is already shifted by beta and must not be shifted a second time. The exact tuple rewrite and all imported source/provider choices still need Lean elaboration in the selected build.

## Existing Lean source route

* `CompactFixedBeta.betaNat` is `2^(67*8807)-1`, and `beta_identity` gives its model cast relation without expanding the numeral. `CompactSymbolicKernelOpaque.paramKernel` defines K by the 943 selector and 41 slot sums; `cast_paramKernel` is the generic cast statement. `CompactSymbolicPorts` defines the two finite mask naturals and the shifted-high fourth component.
* `RetainedBetaBytes.decode_betaBytes`, `CompactKernelByteRecipe.decode_bytes`, `CompactLowByteAssembly.decode_bytes` and `CompactShiftedHighByteAssembly.decode_bytes` state the four base-256 **Lean-list** decoding equalities. `CompactFourPortByteAssembly2.decode_ports` combines them in natural-number order `[beta,K,MC,MF]`; `CompactBytePortsModelIff.byteP_eq` casts the natural decodes to integers and equates them to `CompactSymbolicModelIff.p`. A residue-90 client could use `decode_ports` plus a componentwise integer cast, or the existing `byteP_eq`, once its graph and imported providers are matched. Decode in `ℕ` first: directly elaborating polymorphic `Nat.ofDigits` in `ℤ` is a different term and caused a documented earlier failed join.
* `P72Root.cast_port` and the draft's `cast_port` give the generic cast of an already represented natural tuple to the model difference ring; they do not identify that tuple with filesystem bytes. For the fixed symbolic tuple, `CompactSymbolicPortProjections.beta`, `.kernel`, `.low` and `.high` state the individual model projections. `CompactSymbolicModelUnconditionalIff.model_iff` uses those projections to discharge the four explicit cast hypotheses of `CompactSymbolicModelIff.model_iff`. These are statements about the named symbolic Lean expression, not a new residue-90 graph theorem.

The source files and declaration signatures are pinned by this audit. Earlier independent artifact reviews record successful single-author runs for the K, low, shifted-high, four-port and byte-model pieces, with limited selected-provider and guard checks; they are not a fresh coherent replay for the current residue drafts and do not authenticate every inherited source/object, package, dynamic load or axiom boundary. The 90 client, its parent bridges and the byte-recipe client must be built against a compatible pinned provider closure, with their actual axiom reports checked. A source theorem or a surviving historical `.olean` alone is not sufficient for that join.

## P72/P115 filesystem provenance

The checker independently reads **both** retained P72 and P115 gzip payloads for all four ports, verifies each manifest's exact gzip and decompressed raw SHA-256, lengths and bit counts, and confirms the two copies are byte-for-byte identical. It also checks the raw beta integer is `2^590069-1`. The K raw payload is 74,111 bytes and 592,884 bits. The independently reviewed decimal-port checker reconstructs the selector/slot, low-mask and shifted-high formulas as external integers and matches all four P72 raw values; the source-level K/four-port artifact review separately records the K recipe comparison. These calculations strongly bind the retained tuple externally, but Lean's closed recipe definitions do **not** read gzip files or prove an equality to their contents. A formal file-value claim would need a specified faithful byte-list representation and a proof connecting it to the closed Lean recipes, plus a trustworthy interpretation of the filesystem bytes.

## Display and endpoint boundaries

The separate 13/90 candidate TeX/PDF contains the reviewed compact decimal recipe and 15,086-digit selector seed. This audit replays its independent row/PDF-text receipt and the separate exact decimal-port/byte receipt; these compare the displayed formulas, pinned Lean source expressions and retained bytes externally. They do not furnish a Lean equality between a literal decimal seed and its 943 selector blocks, a formal equation/parser proof, or PDF rendering semantics. For a Lean-defined decimal page expression, the missing finite port equalities remain: beta power form, decimal block extraction against the ordered selector table and kernel slots, low-mask recipe, and once-shifted high-mask recipe. Alternatively, first relate the page-defined naturals to the four closed byte recipes and use `decode_ports`; either path needs the actual Lean definitions and checked equalities.

This compact 13/90 tuple is **not** the maintained root `equation.tex` tuple: the latter says `rho=2^47`, `B=rho^2011` and has beta `2^94517-1`, while compact beta is `2^590069-1`. A source/data association and a checked no-zero comparison (and, if needed, theory/encoding translation) are required before connecting these equations; distinct numerals alone do not decide whether their no-zero statements are equivalent. The pinned source `IPRAOrdinary13.native_equivalence` targets the separate 13-positive 87-operation free-J expression at `CompactSymbolicModelIff.p`, not the 90 graph. The intervening 82/84 and other all-model bridges, symbolic K selection, physical equation link and end-to-end iPRA proof remain open.

Reproduce from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue90-compact-port-provenance-audit/check.py | cmp - reviews/ordinary13-residue90-compact-port-provenance-audit/result.json
```

The command runs only isolated Python and the independent read-only PDF-text/source checks; it does not invoke Lean or prove PDF/file semantics.
