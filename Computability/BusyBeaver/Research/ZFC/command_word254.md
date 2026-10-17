# Numeric words for the actual proof-search commands

[`CommandWord254.lean`](../../Lean/BusyBeaver/ZFC/CommandWord254.lean) gives
a total numeric encoding of finite lists of the actual `Enum254.Cmd` commands,
with exact decoding, tail replacement and concatenation. It supplies the next
finite-data interface for representing the existing proof-to-command compiler
inside arithmetic. It does not yet represent that compiler or prove its
execution contract at nonstandard proof codes.

The shift is essential: the original candidate0 is the real command list
`[MP0]`. The new word encoding reserves0 for the empty list:

```text
encode([])       = 0
encode(c :: cs)  = pack(c,encode(cs)) + 1
                = encL(c,cs) + 1.
```

`encode_decode` and `decode_encode` prove a bijection between all natural
numbers and finite command lists. There are no invalid word codes. This says
nothing about proof validity: the separate proof checker rejects proof code0.
An eventual numeric proof compiler must handle that case explicitly rather
than subtracting1 and accidentally scheduling raw candidate0.

The helpers `tail(z)` and `replaceRest(z,r)` consume an **unshifted candidate**.
They retain its actual command and inspect or replace its rest field. For
operation tags below3, the tail is the second nested right projection; the AX
branch uses four right projections. The all-input formulas retain every
command parameter and agree with the existing exact `pack`/`unpack` codec.

Numeric concatenation obeys:

```text
append(0,right)    = right
append(z+1,right)  = replaceRest(z,append(tail(z),right)) + 1.
```

The existing bound `tail(z)≤z` proves termination. `append_encode` identifies
this recursion with list concatenation; `append_decode` extends the equality
to every pair of natural codes. Associativity, empty-word identities and
replacement identities are also checked.

The [169-unit integration](results/command-word254-integration-verification.json)
freshly checks this module and the umbrella, reusing167 imports with matching
source and object hashes. Its stored audit checks21 named axiom reports and25
callers, using only standard Lean axioms. The
[independent source review](results/command-word254-review.json) checks the
shift, raw-versus-word arguments, four-projection AX branch and all-code scope.
The original enumerator and codec attribution is inherited from `Enum254` and
`EnumStackBarrier254`.

The [arithmetic tail adapter](arithmetic_command_word254.md) now represents
tail/replacement by bounded graphs in every IOpen model. The next extension
can concatenate through a course-of-values history with the right word as
parameter. A subsequent history can pair the exact validity result with the
compiled word for each proof code. Internal execution correctness and the
finite-trace bridge remain separate requirements of the
[PA internalization](pa_internalization.md).
