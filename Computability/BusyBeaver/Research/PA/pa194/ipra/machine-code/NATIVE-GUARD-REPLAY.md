# Native iPRA transfer of a zero-guarded equality

`PA194GuardModel.guardEqual` proves, in every model of candidate PRA, that
`(x = 0 → a = b)` entails `a * isZeroCode(x) = b * isZeroCode(x)`.
It uses model exhaustion, the checked zero-test recursion, and multiplication
by zero; it imposes no restriction on the values of `x`, `a`, or `b`.

`PA194NativeGuard.nativeGuardedOfModels` accepts three primitive-recursive
language terms with the same finite number of free variables, and a Lean proof
that in every candidate-PRA model their interpretations satisfy `a = b` when
the test term is zero. It first proves the universally closed guarded equality
in classical candidate PRA by completeness, then transfers that equality to
`IPRAStandardTheory.standardTheory` via the existing
`PRAEqualityToIPRA.nativeOfClassical` theorem. The conclusion is the guarded
object-language equality itself. It does not by itself recover the unguarded
object-language implication, establish a machine-specific instance, establish
any source execution, or prove a consistency equivalence. In particular the
model premise must hold in every model, not just over standard natural numbers.
Lean axiom audits for both lemmas report `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`; these are Lean metatheoretic assumptions, not
extra axioms asserted inside the object iPRA theory.

## Replay and provenance

`check-native-guard.sh` checks the two source hashes and recompiles them in a
fresh common output directory, auditing both named theorems for `sorryAx`. It
requires a previously built coherent root containing `PRAEqualityToIPRA.olean`,
two prebuilt general project/foundation roots, and the usual prebuilt Lake and
Mathlib objects. It does not rebuild or authenticate those imported objects,
and the source pins alone do not establish compatibility. In this session the
coherent root below was produced by a prior source replay; its extension
manifest SHA-256 is
`24cb6eca676a5a6d74c4ac4a96b4d611b618c907f6b9a698f21a62c088640cc4`.
All indicated roots are session-local and must be replaced by matching roots
when replayed elsewhere. No Git internal environment override is used.

From the repository root:

```sh
base=Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code
bash "$base/check-native-guard.sh" \
  "$PWD" \
  "$base" \
  /dev/shm/pa194-header-coherent/hardlink-baseline \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```
