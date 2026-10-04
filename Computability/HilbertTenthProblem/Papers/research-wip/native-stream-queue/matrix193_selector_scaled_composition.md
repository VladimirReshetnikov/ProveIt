# Compose selector-block sharing with scaled-power reuse

The four complete matrix sources cost **1,417 /1,414 /1,414 /1,411 operations**, with **141 /140 /140 /139 positive witnesses** and exact degrees **35,587 /53,345 /53,347 /71,105**. They combine the [shared selector blocks](matrix193_selector_block_sharing.md) with the separate [scaled-power identity](matrix193_scaled_power_reuse.md). Every entire polynomial equals its immediate selector-sharing parent on identical supplied coordinates over every commutative ring. The established universal84 bound remains unchanged.

The [fresh standalone helper](matrix193_selector_scaled_composition.py) emits all four complete arrays in the [receipt](matrix193_selector_scaled_composition.json). Both arithmetic branch trios and the entry-controller map trio are authenticated as inert files. No frozen program is imported or executed.

## 1. Literal composition and full identity

The immediate parents are the four selector-sharing arrays. In baseline register names, the scaled-power branch replaces

    cp344 = Q^162,
    cp345 = −20*cp344

by the single already-paid-operand product

    cp345 = cp317*cp400 = Q^150*(−20Q^12).

The helper verifies the actual old producer, the new product and the deleted row against the frozen scaled branch for each mapped variant. It freshly expands the relevant pure-Q subcircuits of the selector-sharing parent, authenticates both paid operands, and verifies the exact polynomial identity. Backward liveness removes precisely `cp344` and no other producer.

Dependency scheduling moves `cp400` before its new use; in the three chart listings its `cp333` dependency is advanced too. Acyclicity, sequential operand availability, complete liveness and unchanged relative order of non-pure-Q rows are checked. Every retained definition other than `cp345` is literal.

The whole-source interpreter binds the proved polynomial `−20Q^162` to the full expression of the actual computed Q. Every retained register and the output then has the same formal expression in parent and successor. Thus

    F_composition = F_immediate_selector_sharing_parent

over every commutative ring, without a sign, nonzero-scale, selector-typing or history assumption.

The complete newly scheduled coefficient arrays agree **literally** with the scaled-power branch:552=304M+248A rows per variant. All sixteen full coefficient polynomials and2,704 coefficients are re-expanded and checked. All242=121M+121A shared-selector rows remain literal in their original execution order. The new coefficient dependency therefore neither removes nor duplicates any paid operand of the selector rewrite.

All63 native rows and97 group/population rows remain literal. Both full finalizers are traced from their actual outputs through the native multiplier, one-plus-SOS, every residual square and the complete sum tree. The50/47/47/44 traced rows, including16/15/15/14 residual producers, are identical. The proof does not assume a contiguous source suffix.

## 2. Complete ledgers and scope

| Variant | M | A | Total | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|---:|
| No controller chart |685|732|1,417|141|35,587|
| Flow |684|730|1,414|140|53,345|
| Population |684|730|1,414|140|53,347|
| Both |683|728|1,411|139|71,105|

The four complete arrays contain5,656 paid binary rows. All rows and supplied ports remain live. Each saves one multiplication from its immediate selector-sharing parent, with unchanged additions. The92-gate selector saving is already in that parent and is not counted again. The positive witnesses, ordinary input, eight fixed coefficient ports,137 distinct integer literals, illustrative fixed bindings and output register are unchanged.

Entire polynomial equality preserves exactly the positive integer zero tuples of each immediate parent. Exact degrees transfer through equality on identical variables for every valid fixed-program specialization. Fresh syntactic degree upper bounds are recorded separately; no new leading-component or dense degree calculation is claimed.

The valid fixed-program numeral recipe and natural ordinary input x>=0 remain inherited. The earlier terminal-carry and IDLE comparisons continue to preserve only the ordinary input. This arithmetic identity does not provide a stronger inverse across those older charts, and arbitrary fixed-numeral assignments are not asserted to define universal programs. No new trajectory, native Pell tuple, optimality theorem or universal polynomial below84 is claimed.

## 3. Fresh evidence and replay

The source and receipt record all nine exact dependency hashes. The fresh receipt is bound to its own helper bytes. Some general utility code was copied as inert text and adapted to this composition; predecessor code is never imported or run. Fresh evidence covers the four complete source reconstructions, all pure-Q values, four input-bound whole-output identities, sixteen full coefficient expansions, four literal selector components, eight finalizer traces, interfaces, topology, liveness and full counts. Prior numerical fixtures are not relabeled as fresh evidence.

```sh
composition_wip=/absolute/path/to/native-stream-queue
python3 "$composition_wip/matrix193_selector_scaled_composition.py" \
  --root "$composition_wip" --expect "$composition_wip/matrix193_selector_scaled_composition.json"
python3 -O "$composition_wip/matrix193_selector_scaled_composition.py" \
  --root "$composition_wip" --expect "$composition_wip/matrix193_selector_scaled_composition.json"
```

The two arithmetic branch trios can instead be read from `--packet-root /absolute/packet/directory`; it defaults to `--root`. Generation uses mutually exclusive `--output`. Duplicate/nonfinite JSON is rejected, receipt equality is recursively type-exact, and explicit guards remain active under optimized Python. No frozen predecessor or repository file is modified.

Fresh generation and fresh normal/optimized exact receipt replays from `/` pass.
