# Internal free renaming and named-binder alignment

Three Lean modules now prove the syntax needed for a later all-internal GEN
proof translation. Labels, counters, binder depths, vectors and formula codes
range over every element of an arbitrary model of IΣ1. There is no restriction
to standard codes or to matrices without free parameters.

The fixed represented map `rename L a k s p` preserves every bound variable.
A free label x becomes x when x<k, becomes k when x≥k and x+s=k+a, and becomes
x+s+1 otherwise. The additive test avoids truncated subtraction in its graph.
Its fixed Σ1 graph, term/vector graphs and total raw extensions are chosen
before the arithmetic model.

The checked syntax laws are

```
R(a,k+1,s)(shift p) = shift(R(a,k,s)p)
R(a,0,s)(shift p) = R(a,0,s+1)p
R(a,k+1,s)(free p) = free(R(a,k,s)p).
```

The last law has the actual one-bound-variable typing premise. The source also
proves typedness, substitution/qVec and negation commutation, and the internal
syntax theorem `shift p=p → R(a,k,s)p=p` for well-formed p. The zero-level law
handles a source primitive SHIFT without postulating a nonexistent inverse
SHIFT rule.

The axiom module proves actual ZF/ZFC axiom invariance. Their chosen finite
Δ1 recognizers contain a finite disjunction of equality with sentence quotes.
SepR and RepR already supply a shift-fixed body and an internal number of
universal binders. Internal induction commutes SHIFT with that binder count;
structural induction then fixes each recognized axiom under R. Actual axiom
closure is a conclusion, rather than an assumed closure of arbitrary semantic
predicates. The proof does not assert that arbitrary internal formulas are
standard.

The binder module proves, at every internal depth d,

```
subst(qVecIter(d,[&0]), shift(bindOneAt(a,d,p))) = R(a,0,0)p.
```

In particular `free(bindOneAt(a,0,p))=R(a,0,0)p`. This is the literal premise
required by the existing target ALL rule for the checked `namedAll` syntax.
It imposes no freshness premise. The decoder's literal zero formula still
contains free label zero; nothing here treats it as syntactically closed.

## Verification and reproduction

The syntax source/audit passed 15 axiom reports and 15 arbitrary-input callers
in 23.278/2.522 seconds. The axiom module/audit passed 6/6 in 2.613/1.828
seconds; binder alignment passed 2/3 in 3.193/1.656 seconds. All stages use only
`propext`, `Classical.choice` and `Quot.sound`, with zero warnings. The two
successors reused the exact passed syntax object. One failed syntax attempt
and five failed axiom-normalization attempts are retained in the history
record, including their source/audit/driver snapshots. The successful evidence
records remain unchanged.

With the pinned built dependency checkout and recorded predecessor objects:

```
python Logic/Interpretability/ZFCinPA/check_model_coded_free_renaming.py \
  --repo "$PWD" --dependency-root /home/codex/src/Proofs --output /tmp/renaming-syntax
python Logic/Interpretability/ZFCinPA/check_model_coded_renaming_successors.py \
  --repo "$PWD" --dependency-root /home/codex/src/Proofs \
  --syntax-evidence /tmp/renaming-syntax/verification.json --output /tmp/renaming-successors
```

The successor guard also supports `--stage axioms` or `--stage binding`.
`--prepare-only` validates identities without invoking Lean. Source/audit,
predecessor-evidence, exact consolidated project-cache and complete external
namespace overrides support relocation. The recorded namespace is a cached
boundary: the guards check the selected source/object identities and actual
first providers, without independently attesting the whole external cache.
No dependency build or download occurs. Explicit Lean 4.32.0 uses one thread
and a 4 GiB limit.

Both final portable override preflights and both relocated project-cache
preflights passed with empty command lists. Five controls rejected Python
`-O`, a nonempty output directory, fake Omega and altered copies of the
BindOne and FreeRenaming objects. Original inputs and copied objects were
rehashed after the controls.

## Remaining proof transport

No theorem here renames arbitrary internal proofs or implements GEN. A
proposed next induction fixes internal a,N and proves, by Σ1 order induction
on the source derivation code d, target derivability for every k,s≤N with
`d+k+s≤N`. Strict child-code bounds pay for ALL's k+1 and zero-level SHIFT's
s+1. Bounded universal quantification of Σ1 derivability is eligible in IΣ1;
no Π2 induction or uniform proof selector is assumed. A represented finite
sequent-image operation and every actual proof-rule case still need to be
constructed and checked. GEN, the twelve source axiom rows, accepted-history translation and the PA
consistency endpoint remain separate. The decoder constructor equations and
the truth/MP proof constructors are checked in their own modules.
