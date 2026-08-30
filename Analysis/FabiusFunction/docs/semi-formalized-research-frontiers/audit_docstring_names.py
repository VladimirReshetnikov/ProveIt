# -*- coding: utf-8 -*-
"""Every declaration a module's docstring advertises must exist.

`audit_crosswalk_names.py` checks the names the LaTeX volumes cite.
Nothing checked the names the Lean module docstrings cite, and those
go stale the same way: a "Main declarations" bullet naming a theorem
that was renamed, or that was planned and never written.  Lean does
not check docstring prose, so this is invisible until a reader trusts
it.  Found once for real on 2026-08-29:
`GeneralizedRealBound` advertised
`norm_generalizedRvachevProduct_ofReal_eq_one_iff_of_pos`, a theorem
that was never written -- the module proves
`norm_generalizedRvachevProduct_ofReal_zero` instead.

Scope, kept deliberately narrow so the signal stays high: only
backticked identifiers inside `* ` bullets of a module docstring, and
only those containing `_` or `.` (so ordinary English in backticks,
and bare type names like `Multipliable`, are not treated as
citations).

Two tiers, because an unqualified name is ambiguous.  A token written
`Fabius.foo` is an unambiguous claim about THIS corpus, so an
unresolved one FAILS.  A bare `foo_bar` may equally be a
root-namespace Mathlib lemma -- `summable_prod_of_nonneg` really is
one -- which cannot be checked without Mathlib's name table, so an
unresolved one is only reported.

Filtered out entirely: mathematical subscript notation (`P_d`, `R_n`,
`A_P`) and bare name suffixes under discussion (`_real`, `_left`).

Exits 1 only on an unresolved `Fabius.`-qualified name.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(
    HERE, '..', '..', 'Lean', 'FabiusFunction'))

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|noncomputable\s+|protected\s+|scoped\s+)*'
    r'(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s+'
    r'([A-Za-z_][A-Za-z0-9_\'!?]*(?:\.[A-Za-z_][A-Za-z0-9_\'!?]*)*)',
    re.M)

MODULE_DOC = re.compile(r'/-!(.*?)-/', re.S)
# `P_d`, `R_n`, `A_P`: mathematical notation, not Lean identifiers.
SUBSCRIPT = re.compile(r"^[A-Za-z]_[A-Za-z0-9]{1,2}$")
BULLET = re.compile(r'^\s*\*\s.*$', re.M)
TICKED = re.compile(r'`([^`\n]+)`')
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*$")

# Namespaces owned elsewhere: a citation into them cannot be checked here.
FOREIGN_PREFIXES = (
    'Mathlib.', 'Real.', 'Complex.', 'Nat.', 'Int.', 'Finset.', 'Filter.',
    'Polynomial.', 'MeasureTheory.', 'ProbabilityTheory.', 'Summable.',
    'Multipliable.', 'HasProd.', 'HasSum.', 'ModularForm.', 'Asymptotics.',
    'Function.', 'Set.', 'Topology.', 'ENat.', 'EReal.', 'NNReal.',
    'Tendsto.', 'Metric.', 'Bool.', 'List.', 'Std.', 'Classical.',
)


def corpus_names(files):
    short, full = set(), set()
    for fname in files:
        text = io.open(os.path.join(LEAN, fname),
                       encoding='utf-8', errors='replace').read()
        for name in DECL.findall(text):
            full.add(name)
            short.add(name.split('.')[-1])
            short.add(name)
    return short, full


def cited(text):
    """Backticked identifiers inside docstring bullets."""
    for doc in MODULE_DOC.findall(text):
        for line in BULLET.findall(doc):
            for tok in TICKED.findall(line):
                tok = tok.strip()
                if not IDENT.match(tok):
                    continue
                if '_' not in tok and '.' not in tok:
                    continue
                yield tok


def main():
    if not os.path.isdir(LEAN):
        print('corpus directory not found: %s' % LEAN)
        return 1
    files = sorted(f for f in os.listdir(LEAN) if f.endswith('.lean'))
    short, _ = corpus_names(files)

    # Module names are legitimate citations too.
    modules = {f[:-5] for f in files}
    modules |= {'FabiusFunction.' + m for m in modules}

    hard, soft = [], []
    total = 0
    for fname in files:
        text = io.open(os.path.join(LEAN, fname),
                       encoding='utf-8', errors='replace').read()
        for tok in cited(text):
            total += 1
            qualified = tok.startswith('Fabius.')
            name = tok[len('Fabius.'):] if qualified else tok
            if name in short or name in modules:
                continue
            if name.split('.')[-1] in short:
                continue
            if name.startswith(FOREIGN_PREFIXES):
                continue
            if name.endswith('.lean') and name[:-5] in modules:
                continue
            if SUBSCRIPT.match(name) or name.startswith('_'):
                continue
            if not qualified and name[0].isupper() and '.' in name:
                continue  # a namespaced name this corpus does not own
            (hard if qualified else soft).append((fname, tok))

    print('== docstring declaration names ==')
    print('modules scanned:        %d' % len(files))
    print('advertised names:       %d' % total)
    print('unresolved (Fabius.*):  %d' % len(hard))
    print('unresolved (unqualified, advisory): %d' % len(soft))
    if hard:
        print()
        print('FAILURES -- these name this corpus and do not resolve:')
        for fname, tok in hard:
            print('  %-42s %s' % (fname, tok))
    if soft:
        print()
        print('Advisory -- may be root-namespace Mathlib lemmas:')
        for fname, tok in soft:
            print('  %-42s %s' % (fname, tok))
    return 1 if hard else 0


if __name__ == '__main__':
    sys.exit(main())
