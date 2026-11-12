CONSTRUCTIVE CERTIFICATE TRANSLATIONS

Run:
    python3 verify_translations.py

The two standalone kernels are:
    zero_seven.py       Existing zero-normal calculus with separate case DI and QI.
    reflexive_base.py   New six-rule calculus: DI is progressive exactly when
                       its normalized zero instance is a reflexive equation.

proof_translations.py is an untrusted elaborator. Neither kernel imports it.
It constructs actual JSON proofs and checks every translated certificate
using the destination kernel. The translations preserve the entire sequent:
number of free numerical variables, retained context, and conclusion.

Implemented structural operations:
    numerical weakening/renaming under all syntax and inference binders;
    hypothesis weakening and cut by recursive certificate transformation;
    simultaneous numerical substitution in the seven-rule calculus;
    admissible guarded substitution through the two explicit translations.

The interesting seven-to-six case is arbitrary equation progress. It retains
the old base E(0), guards E(y) as C(y,0,s(y))=C(y,0,t(y)), and uses the supplied
induction premise after recovering E(y) through derived decoder equalities.
Thus the elaborator does not ignore the induction hypothesis or assume the
desired induction conclusion. The decoder proof uses only successor
computation, equality, and derived Q introduction by cases.

The six-to-seven direction replaces a progressive DI by ordinary QI followed
by case DI. A nonprogressive DI is unchanged. If substitution changes a
nonreflexive zero instance into a reflexive one, the return translation cuts
out the now-provable old base and adds the new progress hypothesis. This
explains why a direct syntax-only substitution is not the admissibility proof.

The executed verification recorded 13 substantive translation/control cases,
16 malformed-input rejection cases, and 86 standalone process checks, including
execution with Python -O. Exact results are in translation_verification.json.
The examples directory contains the actual source, translated, round-trip,
and selected rejected certificates. The tests include a genuinely used
induction hypothesis, a nonreflexive induction base, a nested binder, a retained
outer hypothesis, a nonzero-witness progressive introduction, and guard changes
caused both by variable identification and by zero normalization.

These are finite implementation checks, not a proof-assistant verification.
The mathematical argument for all proofs is the structural translation
established in the accompanying report.
