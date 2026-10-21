# A concrete kernel proof of zero-credit enumeration

`CantorCredit.v` supplies a new standalone formalization of the ordinary
NIP-to-DROP injection already documented in ProveIt's ZC215 candidate. It
uses only the Coq/Rocq standard library. It is a contribution to proof
simplification, not a new 214-state construction or a complete ZC215
correctness endpoint.

## What is now proved

The actual pairing is `Cantor.to_nat (x,y)`, i.e.

    P(x,y) = ((x+y)(x+y+1))/2 + y.

The command fields are literal:

- `DROP`: `[0]`;
- `NIP`: `[1]`;
- `MP x`: `[2,x]`;
- `AX c x y`: `[c+3,y,x]`.

A word is explicitly nonempty. A terminal command is emitted with residual
zero; a nonterminal command with residual `1 + encode(tail)`. In particular,
`encode [DROP] = 0`. The executable decoder consumes at most `n+1`
recursive calls on input `n`, justified by the actual decreasing residual.
There are no hypotheses asserting unique parsing or monotonicity of an
unspecified codec: those properties are proved for these definitions.

The core closed theorems are:

- `encode_injective`: two command words with the same raw code are equal;
- `unique_raw_word`: every natural has exactly one nonempty command word;
- `encode_decode` and `decode_encode`: actual executable round trips;
- `concrete_tag_lowering`: changing a selected NIP to DROP strictly lowers
  the raw code, preserving the remaining commands and fields;
- `lower_injective`: this operation is injective on NIP occurrences, because
  replacing that same position back by NIP recovers its source;
- `exhaustive_schedule_zero_credit`: for every `n,j`, the prefix consisting
  of all candidates below `n` and the first `j` positions of candidate `n`
  has at least as many DROP as NIP occurrences;
- `exhaustive_credit_before_nip`: when position `j` of candidate `n` is NIP,
  the preceding prefix has strictly more DROP than NIP occurrences.

The predicates count occurrences, not distinct command values. Position and
word identity are retained. The last two theorems have no scheduler premises:
the schedule is constructed literally from the concrete decoder. The more
general intermediate `concrete_prefix_credit` theorem permits any finite
set of occurrences closed under complete earlier candidates.

The definition `schedule_cut n j` includes `j` positions of the current
candidate. If `j` exceeds its actual length, the extra positions have no
command and count neither way. A genuine syntactic execution prefix uses
`j <= word_length (decode n)`. This convention makes the final inequality
slightly stronger without changing its application.

## What remains before a ZC215 endpoint

This proof does not import or model the Turing transition table. To obtain
the machine endpoint one must separately establish:

1. the exact source implementation decodes these fields and continuations;
2. its actual candidate refill enumerates precisely 0,1,2,..., with no skipped
   return or wrong control target;
3. the command-level theorem-head invariant uses the proved prefix credit;
4. the source-to-binary positive simulation and complete startup frame;
5. the inherited numerical-calculus/ZFC consistency calibration.

The ordinary ZC215 packet already gives arguments and executable evidence
for those connections, but that is not a compiled endpoint supplied here.
A parser theorem alone does not validate a changed low-level return.

## Why this helps

The abstract prefix-credit file in `alternatives/gc-zc215/prefix_credit/`
leaves the key `lower_push`, `lower_earlier`, and `lower_injective` facts as
hypotheses. The present file proves them with the actual Cantor field
encoding, proves its exhaustive decoding, and constructs the concrete
prefix. Thus it supplies a small reusable semantic interface instead of
candidate-density estimates or finite reserve accounting. AX contributes
zero credit to this proof; no axiom-bundle stack length is assumed.

The primary K215 is still the least risky target for shortening the
already compiled complete proof: its initialized stack is zero, so its
existing safe-store invariant does not require this arbitrary-tail
argument at all. ZC215 is a useful independent semantic candidate, whereas
the M124/FM215 family is the simpler *relative* proof extension.

## Reproduce

From this directory:

    python3 build.py --out /a/fresh/output/directory

The driver serializes compiler access using `/tmp/proveit-proof-compiler.lock`,
compiles the exact source copy, runs recursive `coqchk`, and retains complete
logs and a source-hash receipt. The recorded toolchain is Coq 8.18.0 / OCaml
4.14.1. This is not advertised as a Rocq 9.1.0 replay. The standard-library
source imports contain no project-specific dependency or additional axiom.

The `verification-final/` logs are the final successful run; earlier local
compilation attempts are development history and need not be distributed.

## Attribution and provenance

The mathematical injection and its ZC215 application are inherited from:

    Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/
      zero-credit/proofs/tag_lowering_credit.md

The prior generic prototype is:

    Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/
      gc-zc215/prefix_credit/PrefixCredit.v

Both were inspected at ProveIt commit
`53269bcab1efc0f82d3022645bd7cf0c22d84959`. `CantorCredit.v` is an original
concrete formalization prepared for this report; it does not claim discovery
priority for the injection itself. `incoming_inventory.json` pins the seven
current incoming proposals considered in the comparison. Name-search results
in that inventory are narrowly described and are not a semantic novelty test.
