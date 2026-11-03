# Independent K and four-port source/artifact review

This is a Python-only review of the frozen K byte recipe, the four-port
assembly, and their recorded provider artifacts. It did not invoke Lean or
change author files. The recorded run is `observations/attempt01/`; its command
and exit status are in `terminal.json`, its exact audited script is copied as
`source.py`, and stdout contains full hashes and counts. Re-run from the
repository root with `python3 -I -S -B` on `audit.py`. The script requires the
exact historical `/tmp` providers and selected symlink targets recorded by the
author receipts; the checked-in receipt is evidence of this run, not a promise
that those temporary artifacts survive on another machine.

## Result and scope

* The author source and recorded object for `CompactKernelByteRecipe` match
  their accepted receipt; the logged Lean statement decodes 74,111 locally
  computed byte windows to `paramKernel rho`. The source establishes the upper
  bound through `TopDigit.kernel_bounds.2` and applies the generic radix-window
  reconstruction. This review checks the source, selected artifacts and
  receipt; it does not independently replay Lean or authenticate the full
  source-to-object history of every historical dependency.
* The four-port Lean source assembles the lists in order beta, K, MC, MF, and
  its `decode_ports` equality has codomain `Fin 4 → ℕ`. Thus each
  `Nat.ofDigits 256` there produces a natural number. The result is
  `ports betaNat (paramKernel rho) lowNat highNat`, where `ports β K L H` is
  `![β, K, L, β + H]`. MF is already decoded as `betaNat + highNat`: the
  assembly uses that once and does not add beta again. The separately reviewed
  model bridge explicitly casts the natural decoder result to `ℤ`; this does
  not change the decoding operation into an integer decoder.
* The K selected manifest, SHA-256
  `5a91a831350a782f68c8d53ad3e3cb3a828472be6a2eab549293e3b9b6f16427`,
  records five provider roots and 361 selected files. Their live inventories
  matched the records, with zero same-name overlaps among those roots and no
  suppressed companions. The K, MC, and MF selected manifests contained 361,
  606, and 590 files. Every shared filename matched by SHA-256: 345 for K/MC,
  345 for K/MF, and 586 for MC/MF. The 630-file producer union and the
  631-file union including the generic tuple object matched their recorded
  selected sets and hashes; the final manifest hash is
  `14edb04f5ec3bf572cf8a1cf07c35a80d0ac0b5726c3e4affac6797d57d82c42`.
  Six producer source, log, receipt and object records and their recorded
  direct/companion guards were checked, including beta and the generic tuple.
  Selected files, provider inventories and guards were sampled again after
  the arithmetic. These hash and guard checks are external observations, not
  Lean proofs of compilation provenance or continuous monitoring.
* Independently of the author's local two-radix-digit byte routine, the audit
  parses the pinned 943 ordered rows and 41 copy slots and expands the weighted
  power formula for the complete K natural number. Each selector's subtraction
  was checked to be in range. The resulting 592,884-bit integer serializes to
  exactly all 74,111 little-endian retained raw K bytes, SHA-256
  `c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e`.
  Changing one parsed row changes the integer. The author `check_recipe.py`
  was also rerun in isolated Python; it exited 0 with byte-identical output to
  its recorded run. The restored supplement's K gzip and `BINDING.json` were
  byte-identical to the retained parent copies. The binding's SHA-256 is
  `dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01`;
  the compressed K file's SHA-256 is
  `b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a`.

The independent arithmetic is a check of pinned source text, JSON, gzip bytes,
and the parsed formula using Python integers. It is not a Lean equality between
a filesystem payload and the recipe, nor a proof that the PDF displays that
payload. The four-port theorem concerns its Lean list definitions; it does not
by itself internalize their decoding in iPRA or prove the end-to-end
consistency equivalence. For MC, MF, and the later model bridge, consult their
separate source reviews; this packet checks their immediate producer receipts
and the assembly interface, not all their internal derivations.

The audit script SHA-256 is
`317cccc35d2317ef5256b971b9da3759cd20e6502f9be64c67cc3ed584f363de`;
the recorded stdout SHA-256 is
`820e3ab64f8ab9d5ed5ab62084714f2701715b24a56be665b3b8214847515dfd`.
