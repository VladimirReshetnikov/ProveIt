# Sign17 external document and coefficient-byte binding: design

The exact-degree and iPRA endpoints refer to Lean's symbolic expression and
`CurrentWindowCarry2011.ports`. Separately, the external candidate's pinned
`seed.json` has SHA-256
`0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac`.
The staged source generator and its independent source-AST checker compare
all 35 shared nodes and eight rows with that JSON. This is useful external
transcription evidence, not a kernel theorem that parses the JSON or proves
its equation equals Lean's expression.

The JSON describes four minimal unsigned big-endian binary values, in port
order `beta`, `K0`, `MC`, `MF`. The symbolic Lean tuple is `[beta, K,
lowPort, highPort + beta]`; in particular the last source port includes the
beta shift. The candidate checker verifies gzip and raw SHA-256 and lengths,
but does not establish all four raw integers equal the symbolic Lean values.
The [read-only beta check](check-beta-bytes.py) independently reads the pinned
JSON, decompresses the referenced gzip bytes, checks both hashes, and verifies
that its 11,815-byte result is `1f` followed by 11,814 `ff` bytes and equals
`(2^47)^2011 - 1`. It exited 0; [beta-result.json](beta-result.json) records
its output. Checker SHA-256:
`f3a38d3234f4cea4362e175c45cac9695c22c4369b5f72951e6ed2fd08a56277`;
result SHA-256:
`4f51199c8d2221ebb511a78155c8d0cb110d4897d089f644cf8e8e7c19cb5db4`.
This is a Python/OS observation, not a Lean theorem about gzip, hashes or files.

A rigorous staged approach is:

1. Give a total Lean decoder from a finite byte list to its unsigned big-endian
   natural, and prove the symbolic port equals the decoded frozen byte list.
   The beta pattern has a compact parametric representation, so the source-only
   beta probe can prove its numerical equality without constructing 11,815
   individual digits. Prove the other three ports separately, with chunked
   certificates if needed for the much larger kernel and masks. Each theorem
   must name the exact symbolic port, especially `highPort + beta` for MF.
2. State precisely how the finite byte list is bound to the pinned gzip file.
   A build guard can independently hash gzip, decompress it, compare raw
   bytes to the embedded fixture and retain the snapshot; that is an external
   build-provenance check. A theorem about the bytes is purely mathematical;
   it does not itself assert facts about a mutable filesystem. Proving gzip
   decoding and hashes in Lean would require a separate total verified
   decoder/hash checker and a statement over the embedded gzip bytes.
3. For JSON, embed the exact frozen text or an explicitly specified byte
   snapshot and implement a total, fuel-bounded JSON/AST extractor with a
   kernel-checked result equating every decoded row to the staged Lean rows.
   Stage proofs by row and retain port-index and witness-index checks. The
   built-in `Lean.Json` parser uses opaque `partial def`s, so its computed
   result cannot simply be discharged by kernel reduction. The `include_str`
   elaborator reads a UTF-8 file into a kernel literal: a guard must pin what
   was read; this alone proves neither an ongoing filesystem fact nor the
   semantics of gzip. Raw coefficient bytes are not generally UTF-8.
4. Only after both paths are established, compose the AST-row theorem, exact
   port-byte theorems, the Fin17 input-removal/seed assembly, and the existing
   iPRA endpoint/exact-degree theorems. Separately verify whichever rendered
   equation or PDF is claimed to display those exact data.

The scope of each new checked theorem and of every external provenance check
must remain explicit. No JSON-to-Lean, gzip-to-Lean, whole-port or PDF binding
is claimed here.

A second read-only [mask recomputation](check-mask-bytes.py) transcribes the
current low-support sets and high-digit list formulas and independently checks
that the resulting low mask and `highPort + beta` numerically equal the raw
big-endian MC and MF snapshots. It exited 0; [mask-result.json](mask-result.json)
records both gzip/raw hashes. Its checker SHA-256 is
`55c554248c691fa91e2522c7d70d660ff25e38324c60cdc9aba4c1a14ab3eb99`;
result SHA-256 is
`756ff0fb9b305826e1a11a7ca09e05c2ed2df26cacd007555786b9769dbbf3b0`.
This recomputation manually transcribes the Lean definitions and is external
Python evidence; it is not a kernel proof that either raw file equals a Lean
port. The K0 byte equality has not been checked by this script.
The [independent mask review](../../reviews/nine-sharing-sign17-external-masks-independent/README.md)
passed and the external design packet is frozen. The review independently
checked the inspected Lean recipes and raw bytes, but does not turn the
external observation into a Lean theorem.

## MC chunking after the bounded failure

The [split diagnostic](../nine-sharing-sign17-mc-byte-staged-check/attempt01/README.md)
independently established that Lean can elaborate the exact MC-sized numeral
and prove its reflexivity; the separate whole-mask computation overflowed its
stack. This does not isolate the exact internal operation within that proof.
A compositional approach should use the existing checked
`LowMaskCoding.ofDigits_maskList` theorem instead of reducing the 978-element
support sum in one step. With `r = 2^47`, the 2011 little-endian radix digits
are proposed to have runs of `r−2` and `r−1` of lengths respectively
`951, 9, 26, 18, 1, 1006`; the alternating values start with `r−2`.
Proving this sequence equals the actual `maskList` remains an open Lean task.

Eight radix digits are exactly 376 bits, or 47 bytes. Read-only inspection of
the frozen raw MC bytes, reversed to little-endian, finds 252 blocks: 251
47-byte blocks and a final 18-byte block. Their exact byte-pattern runs occur
at block ranges `[0,118)`, `[118,119)`, `[119,120)`, `[120,123)`,
`[123,124)`, `[124,125)`, `[125,126)`, `[126,251)`, `[251,252)`; the first
and fourth share a pattern, as do the all-ones ranges. These run counts and
proposed correspondence are external observations, not Lean theorems.

A bounded proof can establish the few distinct 8-digit/47-byte block
identities separately, prove a general `ofDigits` append/repeat composition
lemma, and use the mask membership theorem with the displayed support
intervals to derive the radix-digit run sequence. The final equality must
still explicitly connect the composed abstract byte list to the literal and
the symbolic current port. The fixed gzip/raw/source checks remain external
provenance until a separate Lean theorem about the embedded file bytes is
constructed; no full MC byte binding is claimed by this plan.
