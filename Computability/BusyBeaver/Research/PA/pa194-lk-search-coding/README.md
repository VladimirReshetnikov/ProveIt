# PA194 source-search numerical coding

This package chooses explicit codes for the PA194 source language: there are
no function symbols, and the two binary relations have codes zero and one.
It proves that the language is arithmetically definable and applies the
current Foundation formula encoding and quote theorem to obtain

```
encode (Semiformula.shift p) = Bootstrapping.shift language (encode p).
```

`encoded_selected` proves that searching the list of natural-number formula
codes returns the code of the exact formula chosen by the universal-rule list
compiler, whenever its membership hypothesis holds. This equality is
unconditional. `numeric_search_primrec` shows that the numeric list search is
primitive recursive **provided** Foundation's numeric shift function for this
language is primitive recursive. It does not assume a `Primcodable` instance
for Foundation formulas.

The source-language encoding instances have no axioms. The code/search
results depend on `[propext, Classical.choice, Quot.sound]`, with no
`sorryAx`, in the checked ordered overlay. The full nested standalone script
has not yet been replayed.

Primitive recursiveness of numeric shift itself, coding of the complete LK
compiler, arithmetic internalization of compiler correctness, and the PA194
machine calibration remain open. This is a standard-Lean result and does not
by itself prove a reduction in PA or PRA.

To rebuild the prerequisite chain from the repository root, set
`IPRA_FOUNDATION_OVERLAY` to the audited current Foundation object overlay and
run `bash Computability/BusyBeaver/Research/PA/pa194-lk-search-coding/check.sh`.
The script uses a temporary tmpfs directory by default.
