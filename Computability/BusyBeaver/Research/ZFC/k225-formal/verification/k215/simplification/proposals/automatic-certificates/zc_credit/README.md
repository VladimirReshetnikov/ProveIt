# Concrete, kernel-checked zero-credit enumeration

## Result

`ConcretePrefixCredit.v` proves the exact unbounded prefix-credit theorem for
the **existing ZC215 command codec**. It uses only Coq's standard library and
has been compiled with Coq 8.18.0 and recursively checked by `coqchk`. It does
not provide a new binary machine, an exact-table ZFC endpoint, or a 214-state
construction.

The generic tag-lowering argument was already in the repository's
`candidate-k215/alternatives/zero-credit/proofs/tag_lowering_credit.md`.
The GC-ZC215 packet contained an uncompiled 107-line `PrefixCredit.v`
formalizing finite counting under hypotheses about the lowering map.
The present contribution proves those hypotheses for the literal codec,
constructs the total parser, defines the actual finite scheduler prefixes,
and checks the resulting closed theorems in the kernel. It does not claim
the underlying injection idea as new.

The reviewed snapshot is
`53269bcab1efc0f82d3022645bd7cf0c22d84959` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/53269bcab1efc0f82d3022645bd7cf0c22d84959/Computability/BusyBeaver/Research/ZFC).
The review also included all seven incoming proof-simplification archives
present at that snapshot, including the latest
`K215_Proof_Simplification_2026-10-21 (2).zip`.

## Exact mathematical statement

Let

    P(a,b) = (a+b)(a+b+1)/2 + b.

The command fields are exactly

| Command | Fields |
|---|---|
| DROP | `[0]` |
| NIP | `[1]` |
| MP(x) | `[2,x]` |
| AX(c;x,y) | `[c+3,y,x]` |

`emit(k,r)` nests those fields through Cantor pairing, ending in `r`.
Define `code([])=0` and `code(k::w)=1+emit(k,code(w))`.
For a nonempty word, its raw candidate number is `code(w)-1`.

The executable parser `word(n)` is proved to satisfy

    code(word(n)) = n+1,
    word(code(w)-1) = w                 for every nonempty w.

The explicit convention matters: `word(0)=[DROP]` and
`word(2)=[DROP,DROP]`. A trailing zero tag is a real command, while the
separate residual zero marks the empty continuation. The proof does not
confuse these cases.

For each NIP occurrence `(n,j)`, replace that NIP with DROP in `word(n)`.
Re-encode the result as candidate `m` and map `(n,j)` to `(m,j)`.
The kernel proves:

1. The image is a DROP occurrence.
2. `m<n`, by strict coordinate monotonicity of Cantor pairing.
3. The map is injective, since restoring NIP at position `j` recovers
   the original word and its raw code.

`prefix(n,j)` lists every command occurrence in candidates `0,...,n-1`
and positions `0,...,j-1` of candidate `n`. `pops(n,j)` and `pushes(n,j)`
are its filters for NIP and DROP. The principal closed theorem is

    every_prefix_has_credit n j :
      length(pops n j) <= length(pushes n j).

There are no codec, monotonicity, injectivity, enumeration, or distinctness
hypotheses. The result even holds for `j` larger than the current word's
length, because invalid occurrence positions contribute to neither filter.

The stronger theorem needed by stack safety is

    credit_before_each_pop n j :
      Pop(n,j) -> 1 + length(pops n j) <= length(pushes n j).

All mapped DROPs occur in strictly earlier completed candidates, so the
current NIP can be included among the sources while only previous pushes
are included as destinations. Consequently an explicit protected-height
invariant

    pushes <= height + pops

implies `height>0` immediately before every NIP. This last implication is
the compiled corollary `protected_head_available`.

Six printed assumption reports (both codec inverses, injection, both
credit theorems, and the protected-head corollary) are closed under the
global context. No classical axiom, admitted proof, project assumption,
or test-derived premise is used.

## Reproduction

From this directory, with `coqc` and `coqchk` on PATH:

```sh
python3 verify_concrete_credit.py --out /tmp/zc215-concrete-credit-check
```

Use a fresh output directory. The script copies the source into that
directory, compiles it, requires all six closed assumption reports,
recursively checks the resulting proof object, and writes exact commands,
source hash, exit codes and raw logs. No network or repository checkout is
required.

The included `verification/result.json` records a successful fresh compile
and recursive kernel check. The build took 5.215 seconds and the recursive
check took 74.897 seconds on the preparation host; these are measurements
of this small module, not projected speedups for ProveIt's full build.

## Finite binding to the literal source

The supplementary `check_parser_binding.py` extracts the **actual proved
Coq parser** to OCaml, runs candidates 0 through 999, and compares every
command and field with the pinned ZC215 mathematical parser. It also
interprets the literal 4,752-leaf source using two independently agreeing
control-flow resolvers. All 4,000 isolated field-reader cases, 1,000 refill
cases, 1,000 positive-continuation cases, and 1,000 dispatch cases pass:
19,686,389 literal source transitions in total. Raw zero and a trailing
zero tag are explicitly exercised. `parser_binding/result.json` binds the
Coq source, extracted output, literal source and reference models by SHA-256.

This finite check reduces the risk of a convention mismatch, but it is not
an all-natural proof connecting this module to the complete source or binary
machine. In particular it checks isolated reader contracts; it does not
execute entire AX/MP command bodies.

To reproduce it, use a pinned ProveIt checkout and OCaml's `ocamlc`:

```sh
python3 check_parser_binding.py \
  --zc /path/to/ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k215/alternatives/zero-credit \
  --out /tmp/zc215-parser-binding-check
```

## Integration boundary

This proves the exact codec/scheduler theorem, not the entire ZC215
correctness theorem. The remaining source-level integration is to connect
the implementation's command parser and refill loop to this exact codec,
then preserve the usual logical witness consisting of theorem heads above
an arbitrary opaque stack tail. DROP contributes one head, NIP consumes
one, and MP and AX must not reduce the count beyond this conservative
assignment. Existing ZC215 has these contracts. AX can be assigned **zero**
credit in this argument; deleting AX outputs would still require a separate
calibration and completeness proof.

The logical prefix witness is intentional. Because `P(0,0)=0`, numerical
stack zero can represent arbitrarily many explicit truth heads over a zero
tail. A physical numeric stack-height measure would therefore be the wrong
invariant. The witness stores the explicit list mathematically and uses
the exact left inverse of pairing when a head is read.

The binary-source simulation, literal blank startup, numerical calculus
calibration, and ZFC equivalence are inherited or still require integration.
No assumption report from this small module should be presented as the
assumption report for a new full ZC215 endpoint.

## Which 215-state candidate is easier to prove?

There are two distinct answers.

**For the shortest incremental certificate, use CM215.** The latest incoming
packet already supplies a checked Lean transfer from CM215 to the literal
certified primary K215, including its dense/Core semantics. Its extra
mathematics is a three-clause marker invariant and positive-duration
simulation for six changed rows. It reuses the entire existing source,
calibration and startup proof. The final full-ZFC adapter in that packet
was supplied but not compiled by that packet's author, so its exact stated
boundary must be retained. Primary K215 remains the baseline.

**For a simpler scheduler proof, use ZC215.** It retains the inherited
calculus and command bodies but admits the concrete injection above.
GC-ZC215 additionally changes the generalization binder and introduces
another conditional decoder merge; ST215 changes the command interface and
needs a protected partial-AX startup. Those changes can be useful for state
search, but they create obligations that the simpler ZC215 scheduler theorem
does not remove.

| Candidate | Main extra obligation | Recommendation |
|---|---|---|
| Primary K215 | Existing complete checked foundation | Keep as canonical endpoint |
| CM215 | Small local marker simulation, already checked in incoming packet | Best marginal proof reuse |
| FM215 | Four-row local marker simulation, checked at native-table level in incoming packet | Simpler local invariant, but dense/Core adapter remains to be compiled |
| ZC215 | Exact exhaustive scheduler + modified startup | Best simple scheduler branch |
| GC-ZC215 | ZC scheduler plus changed generalization and decoder fold | Use only if those changes help state reduction |
| ST215 / DR215 / FT215 | Changed command compiler, credit and startup contracts | Research branches, not the default proof simplification |
| R41 / shallower decoders | New address/source correspondence and binary proof | Lower depth alone does not show a shorter complete proof |

The distinction prevents a misleading claim that fewer rows or a smaller
source automatically mean less proof. CM215 is easier because it admits a
short proof **relative to an already certified machine**. ZC215 simplifies
one mathematical layer but currently has a larger remaining integration gap.

Literal table counts were freshly checked in `candidate-comparison.json`:
each of K215, commands120, CM215, FM215 and ZC215 has exactly 215 working
labels and 430 rows. CM215 changes six rows of primary K215; FM215 changes
four. ZC215 changes two rows of commands120 and also changes its initial
native control from 0 to 74. Comparing ZC215's two-row patch directly to
primary K215 would be misleading because commands120 already has its own
source/table reallocation.

## Follow-up questions

1. Instantiate this parser with the repository's literal source command
   semantics and derive the protected-tail invariant in both proof lanes.
2. Reuse the same theorem for any same-arity, lower-tag push/pop pair under
   an injective strictly monotone nested codec. The concrete theorem here
   can serve as a regression target for that abstraction.
3. Identify physical optimizations that exploit the protected-tail witness
   or unused AX credit. The theorem alone does not justify removing a
   command or an axiom output.
4. Make the checker accept generated source correspondence data rather
   than long explicit certificates, while keeping its kernel soundness
   theorem unchanged.
