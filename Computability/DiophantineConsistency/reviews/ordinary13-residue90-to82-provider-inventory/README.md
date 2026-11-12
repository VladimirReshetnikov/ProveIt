# 13/90 to 82: bounded source and provider inventory

This is a read-only inventory of the literal import closure rooted at the
research draft `Residue90To82Transport`. It is not a build plan, a Lean build,
a provider authentication, or an axiom audit. `inventory.json` pins every
selected source, its literal import list, a dependency order, and bounded
source/object observations. Run `python3 -I -S -B check.py` from any working
directory to check the snapshot. The checker reads the recorded files; it
never creates, removes, selects, or authenticates a provider. A change to an
observed object or source makes it fail rather than silently updating the
snapshot.

The 21 reachable research modules are represented by 17 `.lean.src` drafts
and four `.lean` research sources. All lie outside the Lake project source
root. No corresponding root-level object was observed at
`.lake/build/lib/lean/<module>.olean`. This path check does not exclude an
object in another root, search path, retained overlay, or package.

The immediate non-research frontier consists of 14 qualified project modules
and three Mathlib tactic modules. All 17 observed source paths exist. No
project frontier `.olean` was observed in the standard workspace object root;
all three Mathlib tactic `.olean` files were observed at the Mathlib package
object root. Both presence and absence are bounded observations at the paths
in `inventory.json`, not claims about all filesystems, actual Lean search
precedence, compatibility, or loadability. The recorded toolchain is the
repository's `lean-toolchain` (`leanprover/lean4:v4.32.0`), not evidence that
any object was produced by that toolchain. Other required object sidecars and
the frontier's own transitive imports have not been inventoried.

The main lexical edges are:

```
Residue90To82Transport
  -> Residue82Residuals -> Residue82Literal
  -> Residue90FyForce -> Residue90XZeroGraph
     -> Residue90XZeroArithmetic
     -> Residue90FirstNormJ -> Residue90FirstNormGap
        -> Residue90GraphNorms -> Residue90Residuals -> Residue90Literal
        -> Residue90CompactGraphGamma -> Residue90GraphGamma
           -> Residue90GammaModel -> FirstMainLargeK
              -> MainSquareGap, AuxRootBounds
           -> GammaZeroNarrow
```

This drawing omits some direct imports; the JSON contains the complete
literal edge lists, including `AQ17Forced105Arithmetic`, signed norms,
compact-port bounds and all 17 direct qualified frontier imports. Four older
research providers were selected from their original draft directories. A
bounded filename scan at inventory time found 8 copies of `AuxRootBounds`, 8
of `FirstMainLargeK`, 5 of `GammaZeroNarrow`, and 8 of `MainSquareGap`; each
set had one distinct source hash. This observation does not authenticate
objects or exclude future alternatives.

A future coherent build would need an explicitly selected module-to-source
mapping and a compatible search path for these unqualified names, an
appropriately ordered and complete provider closure including all qualified
transitive dependencies, and authenticated source/object/toolchain provenance
for all prebuilt objects. In particular, a nearby older natural79 overlay or
its recorded provider plan cannot be substituted solely because it contains
some similarly named sources. No materialization or rebuild is authorized by
this inventory, and existing evidence is not modified. At the time of the
read-only inspection `df -h .` showed approximately 4.1 GiB available, below
the existing 5.1 GB guard; this transient observation is not encoded as a
fixed receipt.

The proposed theorem `Residue90To82Transport.native_equivalence` explicitly
requires a `PolynomialBridge` for the **positive-shifted 82 expression** at
its compact-shaped four-port tuple `ports K`, with arbitrary natural `K`.
The separate retained `Compact44.IPRAOrdinary13.native_equivalence` concerns
its own 13-variable, 87-operation expression; it supplies neither the 82
bridge nor a graph equivalence by name alone. Theory/encoding compatibility
and the graph-transfer proof remain separate obligations. The symbolic compact
tuple chooses `K = paramKernel rho`; the separate inert tuple-client draft
proposes that specialization and a byte-tuple comparison, but is not imported
by this closure. Closed-byte/numeral equalities, actual payload provenance,
current PDF semantics, and their connection to the expression are independent
boundaries. None is established by hashing or provider inventory.

The source drafts, including the endpoint and tuple client, remain
unelaborated in this audit. Nothing here establishes either direction of an
iPRA theorem or the intended end-to-end proof.
