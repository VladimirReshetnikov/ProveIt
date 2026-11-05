# Independent review: current2011 kernel byte recipe

**PASS**, within the recorded provider and external-file boundaries. This read-only review did not rerun Lean. The source theorem `rawWord_recipe` proves that the finite physical-order recipe equals `CurrentKernel2011.rawWord r` for arbitrary natural `r`, using the imported selector reindexing theorem. Its 942 selector entries are `weightAt 0 = selectorWeight start` followed by the 941 physical certificate rows; the four control blocks have lengths 8, 9, 8 and 9. `recipe_eq_kernel` specializes the recipe to `2^47`, and `kernel_port` is the definitional port-1 identification. `decode_kernel` applies reverse cancellation and `Nat.ofDigits_digits` to prove that **the symbolic byte-list expression** decodes to that port.

The Lean theorem does not read or decompress a file. This review independently parsed the 59 physical-row chunks and their explicit concatenation, checked 941 unique indices and descending weights, recomputed the Start selector from the literal tile, and reconstructed the recipe as a 2^47-radix coefficient vector using Horner evaluation. The result has 94,941 bits, 11,868 minimal big-endian bytes and SHA-256 `64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7`; it matches both retained gzip payloads externally. The author's external checker was separately rerun read-only and reproduced its recorded output byte for byte. This external comparison is not a Lean theorem about gzip, filesystem contents, TeX or PDF.

The review checked the exact recipe source and compiled source copy, successful dependency and compile exits and log hashes, all 120 recorded direct/companion/shadow slots, the three dependency records and dependency log, the four report names and axiom sets, the compiled object, and the separately observed outer session 98472 exit 0. The author runner records a preflight and provider check before and after; this review does not assert a full transitive dynamic-load trace or independently rebuild the base. The author used Lean `-M2800`, one thread and a 180-second foreground timeout; no automatic group-RSS or host-memory stop was enforced. Attempt01 was an exploratory generic check with no requested object or independent guard; the accepted object is attempt02.

Run `python3 -I -S -B Computability/DiophantineConsistency/reviews/current2011-kernel-byte-recipe-independent/audit.py` from the repository root. The checker revalidates current retained inputs and has no Lean invocation.

| Artifact | SHA-256 |
| --- | --- |
| `audit.py` | `516bf2c2ae060b6730d8f27e2e21b1d0fd775afcdf119670b75a44327aec8805` |
| `result.json` | `6de4eb234086acea96924f697ffb812c44878a62ec82e85ec092717d49ba88f2` |
| reviewed `KernelRecipe.lean` | `13a3b32b1c87156229608a5e8cac2a33a2f85b8b87bec329f35b51cc71ab649a` |
| reviewed attempt02 state | `f752ed2a04fc0ee2638d3687f2555abccf5796f49a10dccf015c05d1a5a0641d` |
