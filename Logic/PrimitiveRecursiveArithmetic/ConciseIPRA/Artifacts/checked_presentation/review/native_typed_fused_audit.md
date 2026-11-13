# Independent audit of the fully typed native checker

Reviewed source: `work/math/native_typed_fused.py`.
Control for the typing fusion: `work/math/native_typed.py`.
The kernel refinement itself is audited in `native_tuple_audit.md`.

## 1. Whole-certificate lexical gate

The gate and driver are:

    p = json.load(open(0))
    q = not set(str(p)) - set('0123456789-[], ') and p.pop
    c(q(), v=1)

For a parsed top-level JSON list, Python prints every nested element using
its representation. Every finite integer/list tree prints using only decimal
digits, a possible minus sign for integers, brackets, commas and spaces.
Conversely, any other JSON element contributes a forbidden character:

- strings contribute quote delimiters (and possibly escape characters);
- booleans and null print as True, False and None, containing letters;
- finite floats contain a decimal point or exponent marker;
- nonfinite floats print as nan or inf (possibly preceded by minus);
- dictionaries contribute braces (and, if nonempty, additional punctuation).

Consequently, on a top-level list, the alphabet test holds exactly for
integer/list trees, including all unused prefixes. A Boolean is not accepted
as an integer leaf.

The alphabet predicate alone is not an exact classifier for arbitrary
top-level JSON: a top-level string such as "[0]" passes it. Such a value has
no .pop attribute and the driver rejects it before entering c. Top-level
integers similarly fail .pop. A top-level dictionary has .pop but fails the
alphabet test; all other nonlist JSON types fail either the alphabet test or
.pop. If the test fails q is False and q() raises. Therefore the complete
gate-plus-driver reaches c exactly with a nonempty top-level list whose
entire tree has integer leaves and list nodes. An empty list is correctly
rejected when the initial goal is popped.

These assertions concern ordinary Python json.load output, not custom
objects with overloaded representations or operators. Finite runtime string
and recursion limits can reject large inputs as ordinary resource failures.

## 2. Redundant initial type check

The removed subexpression is `type(a) is int` within the initial v=1
public-goal traversal. The gate has already proved that every scalar leaf of
the initial goal is an actual integer. The traversal's list branch only
recurses into that goal; a missing image reaches the function sentinel c and
fails during multiplication by zero in either version. Therefore the
removed test is true at every scalar that could be accepted.

After the first public-goal check v is set to zero, so the original type test
was bypassed anyway. Kernel construction can introduce False as a zero image,
but this happens only with v=0 and does not affect the argument. The typed
and fused versions have identical successful traces on gated inputs.

## 3. Safe one-byte discrimination change

Replacing `a * 0 == []` with `a * 0 != 0` is exact on all reachable data:

- for an integer (and for a kernel-generated Boolean), a*0 is numeric zero;
  both tests are false;
- for a list, a*0 is []; both tests are true;
- the missing-image function sentinel raises on multiplication in either
  version.

All other supplied data were excluded before checking. The kernel creates
only integer/list trees or the just-mentioned Boolean zero; tuple selection
does not insert its temporary tuple into a tree. Thus this change preserves
successful executions exactly, not merely the theorem set.

## 4. Public Eq/D grammar and scope

While v=1 the inherited validator accepts list arities 1 and 2 at even
formula depth, and arities 1 and 3 at odd numerical depth. These are D/equality
and successor/iterator, respectively. The common depth increment 5-arity
gives the declared two slots for D, numerical entry at equality, and the
iterator/successor slot conventions. There is no ternary Q formula or
surplus truth/zero constructor in the public goal.

Formula-position scalar leaves are rejected because d%2 is zero and the
fallback invokes the failing sentinel. At a numerical position a leaf must
be zero or an odd coordinate at least three, and must lie below the current
depth. Since the initial floor is zero, negative free parameter names are
excluded. These conditions give precisely the native Eq/D public grammar
with the inherited protected-slot convention. Dummy zero slots may have
their stipulated zero denotation; this is a scoped representation, not a
claim that every denotation has a unique raw spelling.

Every ordinarily compiled canonical native goal satisfies these conditions.
All canonical certificates consist of integer/list data, so the lexical gate
does not remove any theorem furnished by canonical compilation. Combined
with `native_tuple_audit.md`, the resulting 679-byte checker (or its 678-byte
discrimination refinement) is sound and canonically complete relative to the
inherited native calculus and its iPRA bi-interpretation.

## Verdict

Approved. The whole-certificate gate, type-test deletion and discrimination
refinement compose correctly. State whole-input integer/list validation and
native Eq/D goal validation explicitly. This is a smaller complete checked
presentation of the existing axioms, not a new arithmetic axiom inventory.

## 5. Final strip-based alphabet gate

Reviewed final gate in `work/math/native_typed_strip.py`:

    q = not str(p).strip('0123456789-[], ') and p.pop

For every finite Python string s and fixed alphabet A,
`s.strip(A) == ''` holds if and only if every character of s belongs to A.
If every character is allowed, stripping removes the entire string. If a
forbidden character exists, stripping removes only the allowed prefix before
the first forbidden character and the allowed suffix after the last one;
at least one forbidden character remains. Therefore this gate is exactly
equivalent to the previous set-difference gate on every parsed JSON input,
not only on the intended integer/list trees.

The top-level driver caveat and all typing, scope and completeness arguments
above are unchanged. The strip version is approved, including composition
with the exact `a*0!=0` discriminator refinement (673-byte final profile).
