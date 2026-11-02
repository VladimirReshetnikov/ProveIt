# Contextual rerun of the historical row-match parent chain

The unchanged live row-match audit fails because the endpoint source-closure audit expects historical `ModelCarrierCurrent.lean` bytes. The separate [historical endpoint packet](../historical-endpoint-contextual-audit/README.md) preserves the exact drift, a bounded sparse source view, the failed naive relocation and the contextual endpoint rerun. This packet tests a new, explicitly contextual higher-chain rerun; it does not change the old auditors or present the live unchanged chain as passing.

`contextual-chain.py` loads each of five original audit files from the live workspace only after checking its exact SHA-256. A subprocess proxy routes only the whitelisted nested audit edges: row → lookup; lookup → relabel and permutation; each of those → endpoint. It starts a new isolated Python process for each routed audit and forwards the original subprocess arguments, including the caller's timeout. At the endpoint alone, it rebinds `PARENTAUDIT` to the separately prepared sparse historical view; original audit ROOT, absolute receipt paths, provider objects, guard checks and other subprocesses remain unchanged. Every routed audit's complete JSON must equal its corresponding pinned CHECK. This is a contextual wrapper around original audit bytes, not a literal unchanged invocation and not evidence about the newer live source.

The first prototype actually exited 0 in session 97120. The hardened runner actually exited 0 in session 48043; after adding the nonoptimized isolated/no-site interpreter guard, the packaged runner also exited 0 in session 31306. Its full output matched the row-match CHECK byte-for-byte, SHA-256 `db7690d62441f036f8275f5270416b015c8e0b2cc858de8b48ea19a703755df7`. Controlled wrong target, cwd/view, original audit hash, historical source and interpreter-mode tests fail closed. No Lean ran. Both sessions use the existing `/tmp` provider trees and inherit the endpoint's package-transitive, dynamic, sampled-resource and incomplete axiom-inventory boundaries. All checks are point-in-time.

To rerun after preparing a fresh historical view as documented in the linked packet, from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/historical-row-contextual-audit/contextual-chain.py row /tmp/ipra-historical-audit-review-NEW
```

An eventual replay must explicitly pin and identify this contextual runner and independently reviewed historical view; its own preflight and negative controls must verify the contextual parent receipt. The existing inverse and exclusion drivers that invoke the unchanged live row-match audit are still blocked by source drift. This packet is not a Lean build, reverse word transport, checker calibration, or an iPRA proof.
