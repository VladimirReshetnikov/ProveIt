# -*- coding: utf-8 -*-
"""Pre-flight check: no two corpus modules declare the same name.

Lean catches this itself --- the facade fails with "environment already
contains 'Fabius.foo' from FabiusFunction.Bar" --- but only after a full
build, which on this machine is tens of minutes.  This finds it in about
a second, so run it before building a new module.

It is also a duplication check in the plain sense: a collision usually
means the lemma already exists and the new copy should be deleted and
imported instead, not renamed.  Two real cases, both 2026-08-29:

  Fabius.sum_range_choose_eq_choose_succ   ThueMorseMoments
  Fabius.rpow_neg_natCast_mul              SpectralZetaWeighted

Every corpus module opens `namespace Fabius` and none nests further, so
a flat census of declaration names is enough; `private` declarations are
excluded, since they do not collide across modules.

Exits 1 if any name is declared twice.
"""
import io
import os
import re
import sys

# Declaration names carry subscripts and Greek letters.  On a cp1252 console, printing one
# raises UnicodeEncodeError and the audit dies at the moment it has a duplicate to report --
# so force a UTF-8 stream with an escape fallback rather than let the gate fail silently.
for _stream in (sys.stdout, sys.stderr):
    try:
        _stream.reconfigure(encoding='utf-8', errors='backslashreplace')
    except Exception:
        pass

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.normpath(os.path.join(
    HERE, '..', '..', '..', 'Lean', 'FabiusFunction'))

# Lean identifiers are Unicode.  Restricting these classes to ASCII truncated names at the
# first subscript or Greek letter (`jacobiTheta₂_neg_inv` -> `jacobiTheta`), which made
# unrelated declarations collide and produced phantom duplicates.  Note `\\w` is not a
# substitute: subscript digits are Unicode category No, not Nd, so `\\w` does not match them.
_ID_START = ("A-Za-z_"
             "\u00c0-\u024f"      # Latin-1 supplement + Latin Extended-A/B
             "\u0370-\u03ff"      # Greek and Coptic
             "\u1f00-\u1fff"      # Greek Extended
             "\u2100-\u214f")     # letterlike symbols (ℂ ℝ ℤ ℕ ℚ)
_ID_CONT = (_ID_START +
            "0-9'!?"
            "\u00b2\u00b3\u00b9"  # superscripts two, three, one
            "\u2070-\u209c")      # super- and subscripts
_ID = '[' + _ID_START + '][' + _ID_CONT + ']*'

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:noncomputable\s+|protected\s+|scoped\s+)*'
    r'(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s+'
    # Dotted names are one declaration, not a collision on the prefix:
    # `theorem IsFabius.unique` must not read as declaring `IsFabius`.
    r'(' + _ID + r'(?:\.' + _ID + r')*)',
    re.M)

COMMENT_BLOCK = re.compile(r'/-.*?-/', re.S)
COMMENT_LINE = re.compile(r'--.*$', re.M)


def strip_comments(text):
    """Remove doc comments and line comments.

    Without this, ordinary prose inside a docstring whose line happens
    to begin with `def`, `is`-preceded `lemma`, etc. is read as a
    declaration -- which is where the spurious names `is`, `of` and
    `rather` came from on the first run.
    """
    text = COMMENT_BLOCK.sub('', text)
    return COMMENT_LINE.sub('', text)


NS_OPEN = re.compile(r'^namespace\s+([A-Za-z_][\w.\'!?]*)', re.M)
NS_CLOSE = re.compile(r'^end\s*([A-Za-z_][\w.\'!?]*)?\s*$', re.M)


def qualified_names(text):
    """Yield fully qualified declaration names, tracking `namespace`.

    Modules do NOT all sit in a bare `Fabius`: e.g.
    `SaddleLogAsymptoticTransfer` opens `Fabius.SaddleExpansion`, so its
    `coeff_pow_eq_zero_of_lt` genuinely does not collide with the one in
    `Fabius`.  Keying on the short name reports that as a duplicate; the
    stack is what makes the check sound.

    `section ... end` also consumes an anonymous `end`, so only pop on
    an `end` that either names the current namespace or is bare and
    matched by an open namespace count.
    """
    stack = []
    for line in text.splitlines():
        m = NS_OPEN.match(line)
        if m:
            stack.append(m.group(1))
            continue
        m = NS_CLOSE.match(line)
        if m and stack:
            closing = m.group(1)
            if closing is None or closing == stack[-1]:
                stack.pop()
            elif closing in stack:
                # `end Foo` closing an outer namespace: drop to it.
                while stack and stack[-1] != closing:
                    stack.pop()
                if stack:
                    stack.pop()
            continue
        m = DECL.match(line)
        if m:
            prefix = '.'.join(stack)
            yield (prefix + '.' + m.group(1)) if prefix else m.group(1)


def main():
    if not os.path.isdir(LEAN):
        print('corpus directory not found: %s' % LEAN)
        return 1

    seen = {}
    files = sorted(f for f in os.listdir(LEAN) if f.endswith('.lean'))
    for fname in files:
        text = io.open(os.path.join(LEAN, fname),
                       encoding='utf-8', errors='replace').read()
        text = strip_comments(text)
        # Drop private declarations: they are module-local.
        text = re.sub(r'^private\s+.*$', '', text, flags=re.M)
        for name in set(qualified_names(text)):
            seen.setdefault(name, []).append(fname)

    dups = {n: fs for n, fs in seen.items() if len(fs) > 1}

    print('== duplicate declaration names ==')
    print('modules scanned:      %d' % len(files))
    print('distinct names:       %d' % len(seen))
    print('names declared twice: %d' % len(dups))
    if dups:
        print()
        for name in sorted(dups):
            print('  %-46s %s' % (name, ', '.join(sorted(dups[name]))))
        print()
        print('A collision usually means the lemma already exists.')
        print('Prefer deleting the new copy and importing the old one')
        print('over renaming.')
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
