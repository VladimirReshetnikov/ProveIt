/-!
# The route no audit defends against: a statement that lies

Every other file in this directory obtains `False` by weakening the logic, and
every one is named by `#print axioms`. This file obtains something that *reads*
as a proof of `False` while the logic stays completely intact, and
`#print axioms` correctly reports no axioms at all — because the proof really is
closed. The lie is in the statement.

Category (see `../../README.md`): **escape hatch**, but the one that escapes the
audit rather than the kernel.

This is the Lean counterpart of `../Coq/Spoofing.v`. The systematic lexical
study of the same question — which characters Lean will and will not let you use
to build confusable identifiers — is `../../Audits/Lean/StringIdentity/`.

Toolchain: Lean 4.32.0. Verified by `../verify.ps1`.
-/

/-! ## 1. Shadowing the name

Inside the namespace, `False` resolves to a different constant. -/

namespace Shadowed
def False : Prop := True
theorem looks_absurd : False := trivial

/-- info: 'Shadowed.looks_absurd' does not depend on any axioms -/
#guard_msgs in #print axioms looks_absurd
end Shadowed

/-! ## 2. Claiming a glyph Lean has not claimed

Sharper, because no identifier was shadowed and no existing notation was
overridden. `⊥` is the standard symbol for falsity in most of the literature and
in Mathlib (as `Bot.bot`); core Lean leaves it free, so a `prelude`-free,
Mathlib-free file can bind it to anything.

Overriding a notation core *does* define — `¬`, say — is not available this way:
Lean reports `Ambiguous term` and refuses rather than silently preferring one
reading. That is a real defence, and it is why this section uses a free glyph. -/

namespace Claimed
notation:max "⊥" => True
theorem looks_absurd : ⊥ := trivial

/-- info: 'Claimed.looks_absurd' does not depend on any axioms -/
#guard_msgs in #print axioms looks_absurd
end Claimed

/-! ## 3. Homoglyphs — and Lean's partial defence

The identifier below contains U+0430 CYRILLIC SMALL LETTER A in place of the
Latin `a`. Rocq accepts the same spelling as a bare identifier (`../Coq/Spoofing.v`
§4); **Lean does not**, because `isIdRest` admits Latin-1 Supplement and Latin
Extended-A but no Cyrillic. The bare form is a *parse* error —
`def Fаlse : Prop := True` gives `error: expected token`, which `#guard_msgs`
cannot capture because the failure happens before elaboration. It lives in the
companion file `Spoofing.BareCyrillic.lean`, which `../verify.ps1` asserts is
rejected.

French quotes lift the restriction, and *that* is the reachable form. The
`«…»` are conspicuous in source, which is exactly the finding of
`../../Audits/Lean/StringIdentity/`: every confusable Lean admits requires them,
so the attack survives only where the quotes go unread. -/

namespace Homoglyph
def «Fаlse» : Prop := True
theorem looks_absurd : «Fаlse» := trivial

/-- info: 'Homoglyph.looks_absurd' does not depend on any axioms -/
#guard_msgs in #print axioms looks_absurd
end Homoglyph

/-! ## 4. What actually defends against this

`#print` shows the elaborated statement with constants fully qualified, which
unmasks §1 and §3, and `pp.notation false` unmasks §2. -/

/--
info: theorem Shadowed.looks_absurd : Shadowed.False :=
trivial
-/
#guard_msgs in #print Shadowed.looks_absurd

/--
info: theorem Homoglyph.looks_absurd : Homoglyph.«Fаlse» :=
trivial
-/
#guard_msgs in #print Homoglyph.looks_absurd

set_option pp.notation false in
/--
info: theorem Claimed.looks_absurd : True :=
trivial
-/
#guard_msgs in #print Claimed.looks_absurd

/-! ## The honest summary

None of the three is a soundness defect, and no checker would report anything
wrong — because nothing *is* wrong. `leanchecker` accepts all of them, correctly.

The failure is entirely in the human step of reading a statement, and it is the
failure mode that both systems' assumption-tracking machinery is structurally
unable to catch. A `False` obtained this way is a fact about a reader, not about
a kernel — which is why this directory's ground rules say to state the toolchain,
give a control, *and read the statement*, rather than to trust `#print axioms`
alone. -/
