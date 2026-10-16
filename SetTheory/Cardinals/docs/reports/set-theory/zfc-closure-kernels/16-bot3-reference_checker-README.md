# Equality-free PSC: a complete executable reference calculus

This directory contains a fresh Python standard-library implementation of a
classical Hilbert certificate checker for **PSC alone**. It adds neither
Extensionality nor irreflexivity. Its contradiction target is a primitive
falsity symbol, not a membership formula.

It is an executable reference with an ordinary mathematical
soundness/completeness argument. It is **not a Lean-verified checker**, not a
proof of the PSC/ZFC calibration, and not a compiled binary Turing machine.
No sub-254 state count follows from it. The certificate encoding favors
clarity over size or useful proof-search speed.

## Reproduce

Python 3.10 or newer is sufficient; no third-party dependencies are needed.

```sh
python3 -m unittest -v test_psc_hilbert.py
python3 psc_hilbert.py identity.json
```

`identity.json` is a complete five-line derivation of `(x in y) -> (x in y)`.
The command prints its constructed conclusion and confirms that it is not a
refutation. No unbounded search was run. The optional `--search` command is
a mathematically fair but deliberately impractical semidecision procedure.

## Exact syntax

The language has variables, one binary membership relation, primitive
Bottom, implication, and universal quantification. It has no equality,
function symbols, constants, or assumptions. Variable names are arbitrary
finite ASCII identifiers. Formulae are flat prefix arrays of string tokens:

| Formula | Tokens |
|---|---|
| Bottom | `["B"]` |
| `x in y` | `["R", "x", "y"]` |
| `A -> B` | `["I", ...A, ...B]` |
| `forall x A` | `["A", "x", ...A]` |

The ellipses in the last two rows mean actual concatenation of token arrays,
not JSON ellipsis syntax. Thus `forall x ((x in y) -> Bottom)` is
`["A","x","I","R","x","y","B"]`.

The Python API supplies `Var`, `Rel`, `Imp`, `All`, and `BOTTOM`. The
abbreviations are fixed as follows:

```
not A       := A -> Bottom
A and B     := not (A -> not B)
A or B      := (not A) -> B
exists x A  := not (forall x (not A))
u subset v  := forall z ((z in u) -> (z in v)), z fresh
```

Formula manipulation and equality use the flat token representation. This
avoids a fixed Python recursion-depth bound on formula nesting. In
particular, a test checks 2,500 nested quantifiers. Available memory and
execution time still limit any physical run.

## Certificate operations

A certificate is a JSON array of operation objects. Every operation
**constructs** its conclusion. There is no `ASSERT`, `ASSUME`, arbitrary
axiom, supplied-conclusion, Extensionality, or irreflexivity operation.
Unrecognized operations or extra fields are rejected.

| Operation and fields | Constructed conclusion |
|---|---|
| `K`, formulae `A,B` | `A -> (B -> A)` |
| `S`, formulae `A,B,C` | `(A -> (B -> C)) -> ((A -> B) -> (A -> C))` |
| `C`, formulae `A,B` | `(not A -> not B) -> (B -> A)` |
| `UI`, variable names `x,y`, formula `A` | `(forall x A) -> A[y/x]` |
| `QD`, name `x`, formulae `A,B` | `forall x (A -> B) -> (A -> forall x B)`, only if `x` is not free in `A` |
| `MP`, indices `premise,implication` | `B` from earlier exact `A` and `A -> B` |
| `GEN`, index `line`, name `x` | `forall x A` from the earlier theorem `A` |
| `PSC`, formula `rho`, distinct names `x,y` | The universally closed subset-seeded PSC instance below |

References are zero-based indices to strictly earlier lines. Negative,
forward, Boolean, floating-point, string, and missing references are
rejected. Python's otherwise permissive identification of `bool` with `int`
is explicitly excluded. JSON duplicate keys, floating-point values, NaN,
infinity, invalid UTF-8, and malformed syntax are also rejected.

### Universal instantiation really substitutes

`UI` includes both same-variable and cross-variable instantiation. The
substitution is simultaneous on free variables and capture-avoiding. Before
entering a quantifier that would capture a replacement variable, the
routine chooses the first unused name `_v0`, `_v1`, ... and renames the
bound occurrences in that scope. Nested shadowing is respected.

For example, substituting `y` for the free `x` in
`forall y (x in y)` returns `forall _v0 (y in _v0)`, assuming `_v0` is fresh.
It does not return `forall y (y in y)`. Substituting a name for itself leaves
the formula unchanged. Every name already present, whether free or bound,
is excluded from the fresh-name supply.

### The nonlogical schema

For an arbitrary equality-free matrix `rho(x,y; parameters)`, define

```
SB(rho) := forall x exists b forall y (rho(x,y) -> y subset b).
```

The generated axiom is the universal closure of

```
SB(rho) -> forall a exists C (
    (forall x forall y (
        (((x subset a) or (x in C)) and rho(x,y)) -> y in C
    ))
    and
    (forall y ((y in C) -> exists x rho(x,y)))
).
```

The input in the support clause is unrestricted. In particular, the
generator does not silently strengthen support to an input belonging to
`C` or to the seed. The matrix may contain arbitrary quantifier nesting and
negation, and either designated free slot may be absent.

Each wrapper binder is given a different name absent from **all** variable
names in the matrix. The three matrix copies substitute only its designated
free input/output slots. Other free names are parameters; they are closed
universally in lexicographic order. Existing matrix binders are preserved.
An ordinary parameter can later be instantiated to the same value as a
seed or another parameter; syntactic freshness does not impose distinctness
of objects.

## Why the calculus is sound and complete

Let `PSC` mean the classical first-order theory on a nonempty domain with
precisely all the schema instances described above.

**Soundness.** Each `K`, `S`, and `C` line is a classical propositional
tautology with Bottom interpreted as false. The free-variable substitution
lemma gives validity of `UI`, including its alpha-renaming cases. `QD` is
valid under its checked side condition: the truth of `A` is unchanged when
the assignment to `x` varies. A `PSC` line is an actual universally closed
axiom instance, because fresh binders cannot capture matrix variables.
Modus ponens preserves theoremhood. Generalization applies to a theorem,
with no undischarged assumptions, so it preserves theoremhood for every
variable. Induction on certificate length proves every constructed line a
PSC theorem. An accepted final primitive Bottom is therefore a finite PSC
refutation.

**Completeness.** `K`, `S`, and the displayed classical `C` are a complete
propositional Hilbert basis. With universal instantiation, the displayed
quantifier distribution/vacuity axiom, and generalization, they form the
usual complete equality-free first-order Hilbert calculus. Terms in this
language are just variables, so instantiation by every variable is all
the required term instantiation. Ordinary free-for substitution instances
are included literally; capture-avoiding alpha-renaming additionally
admits the equivalent fresh-binder versions. This is the ordinary
first-order completeness argument, not an assumption that same-variable
instantiation alone is sufficient.

Every finite Hilbert derivation from PSC translates line by line into the
operation list. Each nonlogical line specifies its matrix and two free
slot names; universal closure and fresh wrapper names differ from other
presentations only by the provable alpha-renaming laws. If an axiom is
presented with free parameters, universal instantiation recovers that
instance from its closed version. Hence PSC has a finite refutation iff
some accepted certificate has final line primitive Bottom.

Combining this syntactic equivalence with the separate mathematical
calibration `Con(PSC) <-> Con(ZFC)` would justify a halting equivalence for
an ideal execution of this search. The code itself does not establish that
calibration or certify compilation to another machine model.

## Fair search and decoding

`length_lex_bytes()` enumerates every finite byte string exactly once,
first by length and then in lexicographic order on byte values 0 through
255. `refutes_bytes` rejects invalid encodings, or checks the decoded
certificate and accepts exactly when its last constructed formula is
`["B"]`. Thus each iteration is a finite, effective syntax check, and every
finite valid certificate has an encoding eventually reached by the search.
All valid certificate JSON has bounded structural nesting, because formulae
are flat arrays. Rejecting excessively nested malformed JSON does not
exclude any valid formula depth.

`search_refutation()` halts iff PSC is syntactically inconsistent. Its
runtime is irrelevant to the formal semidecision claim but is so poor that
the command is unsuitable for exploratory theorem proving. No universal
Turing-machine state count or compiler correctness is asserted.

## What was tested

The tests cover a complete K/S identity derivation and generalization;
classical truth-table validity of the propositional basis; ordinary,
same-variable, and capture-avoiding UI; the substitution semantic lemma on
all binary relations on a two-element domain for several formulas; nested
shadowing; exact PSC generation including global support and parameter
closure; malformed formulae; strict references and side conditions; JSON
rejection; and the first length boundary of the fair byte enumeration.

These are meaningful implementation checks, not a proof assistant
verification or a test of consistency. A successful finite test run cannot
prove PSC or ZFC consistent.
