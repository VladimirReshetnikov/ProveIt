#!/usr/bin/env python3
"""Check the two documentation invariants of ``Analysis/FabiusFunction/Lean``.

The project requires

* a ``/-! ... -/`` module header on every source file, and
* a ``/-- ... -/`` doc comment on every non-``private`` declaration.

Both are stated in ``Analysis/FabiusFunction/AGENTS.md``.  Neither currently
holds corpus-wide, so this script exists to make the gap measurable and to let
a reviewer check that a change does not make it worse.  It is the executable
form of the numbers quoted in ``docs/DOCUMENTATION_AUDIT.md``.

Run from anywhere::

    python3 Analysis/FabiusFunction/scripts/doc_audit.py
    python3 Analysis/FabiusFunction/scripts/doc_audit.py --list
    python3 Analysis/FabiusFunction/scripts/doc_audit.py --baseline docs/doc_audit_baseline.json

Exit status is 0 unless ``--baseline`` is given and the corpus has regressed
against it, which makes the script usable as a CI gate once a baseline is
pinned.

This is a lexical check, not a Lean elaboration.  It tracks nested block
comments, string literals and line comments so that declarations quoted inside
comments are never counted, but it does not know about macros that generate
declarations.  ``to_additive``-style generated names are therefore invisible to
it, as they are to a reader of the source.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys

DECL_KEYWORDS = (
    "theorem", "lemma", "def", "abbrev", "instance",
    "structure", "class", "inductive", "opaque",
)

MODIFIERS = (
    "noncomputable", "protected", "scoped", "partial", "unsafe",
    "nonrec", "local", "private",
)

# A column-0 declaration, possibly preceded by modifiers.  ``private`` is
# matched here so that it can be recognized and skipped rather than silently
# treated as public.
DECL_RE = re.compile(
    r"^(?P<mods>(?:(?:%s)\s+)*)(?P<kw>%s)\b(?P<rest>.*)$"
    % ("|".join(MODIFIERS), "|".join(DECL_KEYWORDS))
)

# An attribute line, e.g. ``@[simp]`` or ``@[simp, norm_cast]``, or an
# ``@[simp] theorem foo`` prefix, or ``set_option ... in``.
ATTR_RE = re.compile(r"^@\[")
SET_OPTION_IN_RE = re.compile(r"^set_option\b.*\bin\s*$")


def strip_leading_attributes(code: str) -> str:
    """Remove one or more leading ``@[...]`` blocks from a code line.

    Lean permits an attribute and its declaration on the same line.  A plain
    declaration regexp therefore undercounts public APIs unless the attribute
    prefix is consumed first.  Bracket depth is tracked instead of using a
    ``[^]]*`` regexp, so nested attribute arguments remain harmless.
    """
    code = code.lstrip()
    while code.startswith("@["):
        depth = 0
        end = None
        for i, char in enumerate(code[1:], start=1):
            if char == "[":
                depth += 1
            elif char == "]":
                depth -= 1
                if depth == 0:
                    end = i + 1
                    break
        if end is None:
            return code
        code = code[end:].lstrip()
    return code


def strip_comments(lines):
    """Return a parallel list marking which lines are *code*.

    ``out[i]`` is the code content of ``lines[i]`` with comment and string
    material blanked out, plus a flag saying whether the line begins a doc
    comment (``/--``) or a module comment (``/-!``).
    """
    depth = 0
    doc_open = False
    result = []
    for raw in lines:
        i = 0
        code = []
        starts_doc = False
        starts_mod = False
        n = len(raw)
        while i < n:
            two = raw[i:i + 2]
            three = raw[i:i + 3]
            if depth == 0 and three == "/--":
                if not code and not "".join(code).strip():
                    starts_doc = True
                depth += 1
                doc_open = True
                i += 3
                continue
            if depth == 0 and three == "/-!":
                starts_mod = True
                depth += 1
                i += 3
                continue
            if two == "/-":
                depth += 1
                i += 2
                continue
            if two == "-/":
                if depth > 0:
                    depth -= 1
                    if depth == 0:
                        doc_open = False
                i += 2
                continue
            if depth == 0 and two == "--":
                break
            if depth == 0 and raw[i] == '"':
                # skip a string literal
                i += 1
                while i < n:
                    if raw[i] == "\\":
                        i += 2
                        continue
                    if raw[i] == '"':
                        i += 1
                        break
                    i += 1
                code.append(" ")
                continue
            if depth == 0:
                code.append(raw[i])
            i += 1
        result.append(("".join(code), starts_doc, starts_mod, depth > 0))
    del doc_open
    return result


def decl_name(kw: str, rest: str) -> str:
    rest = rest.strip()
    if not rest:
        return "<anonymous %s>" % kw
    m = re.match(r"[^\s({\[:]+", rest)
    return m.group(0) if m else "<anonymous %s>" % kw


def audit_file(path):
    with open(path, encoding="utf-8") as handle:
        lines = handle.read().split("\n")
    marked = strip_comments(lines)

    has_module_header = any(m[2] for m in marked)

    # ``doc_end[i]`` is True when line i is the last line of a ``/-- -/`` block.
    doc_end = [False] * len(lines)
    in_doc = False
    for i, (_code, starts_doc, _starts_mod, still_open) in enumerate(marked):
        if starts_doc:
            in_doc = True
        if in_doc and not still_open:
            doc_end[i] = True
            in_doc = False

    public, missing = 0, []
    for i, (code, starts_doc, _starts_mod, _open) in enumerate(marked):
        # Attributes may either occupy preceding lines or prefix the
        # declaration itself (``@[simp] theorem foo``).
        m = DECL_RE.match(strip_leading_attributes(code))
        if not m:
            continue
        if "private" in m.group("mods").split():
            continue
        public += 1
        if starts_doc:
            # ``/-- ... -/ theorem foo`` on one line is documented by
            # construction, but still contributes to the public count.
            continue
        # Walk back over attribute lines, ``set_option ... in`` lines, and
        # blank lines to find the nearest preceding doc comment.
        j = i - 1
        documented = False
        while j >= 0:
            prev = marked[j][0].strip()
            if doc_end[j]:
                documented = True
                break
            if prev == "" or ATTR_RE.match(prev) or SET_OPTION_IN_RE.match(prev) \
                    or prev.startswith("]") or prev.endswith(","):
                j -= 1
                continue
            break
        if not documented:
            missing.append((i + 1, decl_name(m.group("kw"), m.group("rest"))))
    return has_module_header, public, missing


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=None,
                        help="the FabiusFunction Lean source directory")
    parser.add_argument("--list", action="store_true",
                        help="print every undocumented declaration")
    parser.add_argument("--baseline", default=None,
                        help="JSON baseline to compare against; a regression exits 1")
    parser.add_argument("--write-baseline", default=None,
                        help="write the current counts to this JSON path")
    args = parser.parse_args()

    root = args.root
    if root is None:
        here = os.path.dirname(os.path.abspath(__file__))
        root = os.path.join(here, os.pardir, "Lean", "FabiusFunction")
    root = os.path.abspath(root)
    if not os.path.isdir(root):
        sys.stderr.write("no such directory: %s\n" % root)
        return 2

    names = sorted(f for f in os.listdir(root) if f.endswith(".lean"))
    total_public = 0
    per_file = {}
    no_header = []
    for name in names:
        has_header, public, missing = audit_file(os.path.join(root, name))
        total_public += public
        if missing:
            per_file[name] = [{"line": ln, "name": nm} for ln, nm in missing]
        if not has_header:
            no_header.append(name)

    total_missing = sum(len(v) for v in per_file.values())
    print("files scanned                : %d" % len(names))
    print("public declarations          : %d" % total_public)
    print("missing doc comments         : %d (%.1f%%)"
          % (total_missing, 100.0 * total_missing / max(total_public, 1)))
    print("files with a violation       : %d" % len(per_file))
    print("files with no module header  : %d" % len(no_header))
    if no_header:
        for name in no_header:
            print("  NO MODULE HEADER: %s" % name)
    print()
    print("worst files:")
    for name, items in sorted(per_file.items(), key=lambda kv: -len(kv[1]))[:20]:
        print("  %4d  %s" % (len(items), name))
    if args.list:
        print()
        for name, items in sorted(per_file.items()):
            for item in items:
                print("%s:%d  %s" % (name, item["line"], item["name"]))

    summary = {
        "files": len(names),
        "publicDeclarations": total_public,
        "missingDocComments": total_missing,
        "filesWithNoModuleHeader": no_header,
        "missingByFile": {k: len(v) for k, v in sorted(per_file.items())},
    }
    if args.write_baseline:
        with open(args.write_baseline, "w", encoding="utf-8") as handle:
            json.dump(summary, handle, indent=2, sort_keys=True)
            handle.write("\n")
        print("\nwrote baseline to %s" % args.write_baseline)

    if args.baseline:
        with open(args.baseline, encoding="utf-8") as handle:
            base = json.load(handle)
        bad = []
        if total_missing > base.get("missingDocComments", total_missing):
            bad.append("missing doc comments rose from %d to %d"
                       % (base["missingDocComments"], total_missing))
        new_headerless = set(no_header) - set(base.get("filesWithNoModuleHeader", []))
        if new_headerless:
            bad.append("new files without a module header: %s"
                       % ", ".join(sorted(new_headerless)))
        for name, count in summary["missingByFile"].items():
            was = base.get("missingByFile", {}).get(name, 0)
            if count > was:
                bad.append("%s: undocumented declarations rose from %d to %d"
                           % (name, was, count))
        if bad:
            print("\nREGRESSION against %s:" % args.baseline)
            for line in bad:
                print("  " + line)
            return 1
        print("\nno regression against %s" % args.baseline)
    return 0


if __name__ == "__main__":
    sys.exit(main())
