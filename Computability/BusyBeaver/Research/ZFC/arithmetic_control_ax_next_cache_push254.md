# Internal AX cache push at controls 354–380

[ArithmeticControlAXNextCachePush254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXNextCachePush254.lean) proves the actual P2/cache push at **354→380**. For every internal register file in a model of IΣ₁, with S1=S2=0 initially, it supplies a positive internal execution time and the exact full-file effect:

- `TW := oldcache`;
- `WS := cantor(oldTW, oldWS)`;
- all other seven coordinates unchanged, including the cache and both scratch coordinates.

The copy/restore tail **373→380** has a separate exact-time contract: it takes `7 * oldcache + 2` internal steps, requires only S1=0, permits arbitrary TW, and changes TW to `oldTW + oldcache` while retaining every other coordinate. These proofs instantiate the checked [generic CopyBack and push contracts](arithmetic_control_copy_back254.md). The occurrence binds 26 executing instruction edges and 34 successors, using 27 cached complete catalogue-source facts including the exit. The generic theorems supply unbounded internal execution; the following AC push is separate.

The [typed audit](arithmetic_control_ax_next_cache_push254_audit.lean) contains six named axiom probes and eight callers. The first actual run passed in 30.368 seconds for source and 1.829 seconds for audit, with zero warnings. The three control facts use `propext`; the three file/execution reports use only `propext`, `Classical.choice` and `Quot.sound`. The [verification record](results/arithmetic-control-ax-next-cache-push254-verification.json) retains exact commands, outputs and fresh-object captures before audit.

The [independent actual-evidence review](results/arithmetic-control-ax-next-cache-push254-review.json) checks all 225 recorded inputs, the exact 99-project import closure, six cached Foundation/Mathlib pairs (five directly imported), and Init/Omega. Its separate source review independently decodes the 27 complete control bindings and 34 successor paths from the full literal tree. That reviewer authored neither this source nor its guard; the source/guard author prepared this publication builder. Root-owned execution, installation and maintained preparation remain separate.

Before execution, four comment lines were corrected to name the actual control ranges, the P2/cache register and the following AC push. Proof tokens and audit bytes were unchanged. [The history](results/arithmetic-control-ax-next-cache-push254-history.json) preserves the original uncompiled source, freeze/inventory/diff, the comment-correction receipt, source and guard reviews, preparation, first actual source/audit PASS, raw logs and root receipts. No failed proof attempt for this module is claimed.

The [provider proposal](results/arithmetic-control-ax-next-cache-push254-provider-proposal.json) pins the generic CopyBack parent and exact source/object pairs. That immediate parent and this unit both recorded their source object and first provider before audit. Earlier ancestor provenance remains explicit; retained alternative objects are historical metadata rather than newly checked providers. Replay requires the exact cached providers. Compiled caches are excluded from this packet, and no clean-checkout dependency rebuild is certified.

The maintained [guard](check_arithmetic_control_ax_next_cache_push254.py) changes only its source, audit and provider-proposal default paths. Preparation performs no compiler or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_next_cache_push254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --copy-back-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-copy-back254-verification.json \
  --output /tmp/fresh-ax-next-cache-push-preparation \
  --prepare-only
```

Omitting `--prepare-only` in a fresh output directory runs source and audit under default proof limits, one thread, 4,096 MiB and a shared 120-second budget. This contract covers the stated push and its tail. The complete AX branch, interpreter/Enum comparison and internal binary consistency equivalence remain separate obligations.

The register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
