# `Name.toString` is not injective — and it is reachable from ordinary source

This is the strongest result of the string-identity study, and the only one that
is a *machine-level* defect rather than a hazard for human readers.

## The collision

`NameToStringCollision.lean`. Plain Lean 4.32.0, no metaprogramming:

```lean
def «a.b»._inaccessible : Nat := 111

namespace a.b
def _inaccessible : Nat := 222
end a.b
```

Two genuinely different constants — one whose *first component is the string
`"a.b"`*, one with components `"a"`, `"b"` — both present in the environment:

```
N1 == N2                        false
(N1.toString, N2.toString)      ("a.b._inaccessible", "a.b._inaccessible")
N1.toString == N2.toString      true
N1.toString.toName == N2        true
N1 -> OfNat.ofNat Nat 111 ...
N2 -> OfNat.ofNat Nat 222 ...
```

So `toString` maps two distinct constants to one string, and the printed form of
the first parses back to the *second*. Ordinal comparison of the printed forms
keeps them apart; `toName ∘ toString` does not. Two notions of name identity in
one system.

## Root cause

`Init/Meta/Defs.lean:245`:

```lean
toStringWithSep "." (escape && !n.isInaccessibleUserName && !n.hasMacroScopes
                            && !maybePseudoSyntax) n isToken
```

A single true disjunct disables guillemet escaping for the **entire** name, so
*every* component boundary becomes unrecoverable — including middle components
that contain a `.`. All three suppressors inspect only the outermost component
or the root, never the middle ones:

* `hasMacroScopes` — final component `_hyg`
* `isInaccessibleUserName` — final component `_inaccessible`, or contains `✝`
* `maybePseudoSyntax` — root component starts with `#` or `?`

`_inaccessible` is the trigger reachable from ordinary source; `def «a.b»._hyg`
panics the elaborator instead (`unreachable @ extractMainModule`), and the `#`/`?`
roots need `«…»` too.

Lean's docstring already warns that names "containing `»`" may not round trip
(`Init/Meta/Defs.lean:235`), but this case involves no `»` at all.

## Why it does not break `comparator`

`Main.lean:135 safeExport` is comparator's only `Name → String → Name`
boundary — it serialises the constants to export with `.toString` and passes
them as **argv** to `lean4export`, which parses them back with
`Syntax.decodeNameLit`. A config entry of `"«a.b»._inaccessible"` therefore makes
comparator ask for one constant and lean4export export a different one.

It still fails closed, for two reasons:

1. The exotic name has to come from the **config**, which the challenge owner
   writes. A solution author controls only the solution source.
2. `Compare.lean:65` and `Axioms.lean:52` then do
   `constMap[target]? | throw s!"Const not found in challenge: '{target}'"` — a
   hard error, never a false accept.

The residual damage is **diagnosability**: `{target}` is rendered by the same
non-injective `toString`, so the error names the constant that *was* exported
rather than the one requested.

## The sharper variant: escape suppression + NUL = arbitrary substitution

Reported by the sweep (Windows; not re-run by me). With escaping suppressed, a
NUL inside a component survives into the argv string, and the OS `char*` contract
truncates there:

```
name      «Nat.add\0ZZZ»._inaccessible
toString  "Nat.add\x00ZZZ._inaccessible"
argv[1]   len=7  bytes=b'Nat.add'
child     parses to  @.str "Nat".str "add"
```

Parent sent 25 bytes, child received 7 — silently, exit 0. That is substitution
of an *arbitrarily chosen existing* constant, not mere re-association. Without
escape suppression the same NUL is harmless: `«nuA` has no closing `»`,
`decodeNameLit` returns `none`, and `.get!` panics, so comparator fails on the
nonzero exit.

Two further quiet failures in the same family:

* **`»` and `✝` components → panic.** `escapePart` returns `none` for these, and
  `maybeEscape` (`Init/Data/ToString/Name.lean:85`) swallows the `none` with
  `.getD s`, emitting the component **raw** — discarding precisely the signal
  `escapePart`'s docstring promises.
* **`--` prefix → silently dropped.** `def «--foo»._inaccessible` stringifies to
  `--foo._inaccessible`; lean4export's `args.partition (·.startsWith "--")`
  reclassifies it as an *option*, so it is never exported and no error is raised.

## Why none of this escalates to unsoundness

The boundary a solution author actually controls — the export payload — is
clean. `lean4export/Export.lean:95 dumpName` emits
`{"str":{"pre":idx,"str":s}}` with the component as a raw JSON string, and
comparator's `Export/Parse.lean:92` reads it back structurally. A fuzz over all
**1,112,064** code points found 0 JSON round-trip mismatches and 0 distinct
characters rendering to identical JSON text. Hierarchy survives even for
dot-in-component names: `axiom «Classical.choice» : False` exports as
`{"str":{"pre":0,"str":"Classical.choice"}}`, structurally distinguishable from
the genuine axiom's `pre=2038` chain.

Comparator's decision logic is structural throughout (`Std.HashSet Lean.Name`,
`Array Lean.Name`) with no normalisation, case folding, collation or
dot-splitting anywhere.
