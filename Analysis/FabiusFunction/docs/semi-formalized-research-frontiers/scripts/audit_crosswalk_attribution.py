# -*- coding: utf-8 -*-
r"""Two checks the existing crosswalk gates do not make.

``audit_crosswalk_names.py`` verifies that every ``Fabius.*`` name cited in the
documents exists somewhere in the corpus.  Two failure modes survive it, and
both send a reader to the wrong place while every other gate passes.

**(A) Attribution.**  A crosswalk note names a module and then names
declarations, and the reader takes the second to live in the first.  Nothing
checked that.  A name that exists but sits in a different module reads as
correct, builds clean, and resolves in the name audit.  This script checks, for
every crosswalk block that cites at least one module, that each declaration
cited in the same block is declared in one of them.  The fix when it fires is
usually to name the other module too, which is better prose anyway.

**(B) Namespace head.**  The name audit examines only citations beginning
``Fabius.``.  A citation such as ``Bell.complete`` -- a real declaration in a
real top-level namespace that is *not* ``Fabius`` -- was skipped entirely, and
so was a citation whose namespace is simply wrong.  This script classifies every
dotted citation by its leading segment: heads that are corpus namespaces must
resolve, heads known to be external are reported, and anything else is reported
so a typo cannot hide among the Mathlib references.

Run from anywhere::

    python3 audit_crosswalk_attribution.py
    python3 audit_crosswalk_attribution.py --list      # every finding
    python3 audit_crosswalk_attribution.py --unchecked # also the external names
    python3 audit_crosswalk_attribution.py --strict    # fail on (A) too

Exit status is 1 on an unresolved corpus-namespace citation, so (B) gates a
commit.  (A) is **reported, not failed**, unless ``--strict``: measured across
this corpus it fires often, and enough of those are legitimate references to a
sibling module that a hard gate would train people to ignore it.  Read it, and
fix by naming the other module.  External citations are reported and never
failed: this cannot know what is in Mathlib.

Three things learned by getting this wrong, all of them about where a match is
allowed to begin and end:

* **External namespaces win over corpus namespaces.**  The corpus opens some
  Mathlib namespaces of its own (``namespace PowerSeries.Implicit``), so the
  head of a citation being a corpus namespace is *not* evidence that the
  citation is ours.  Checking corpus membership first produced 13 false
  positives out of 19.

* **A module may be cited whole or split.**  ``Foo.lean`` in one macro, or
  ``\path{Foo}\texttt{.lean}`` in two.  The split spelling yields the citation
  ``Foo`` with no extension; an earlier version saw no module in such a block
  and reported every declaration living there as misattributed -- seven of its
  first seventy-two findings were that artifact.  Both spellings are accepted
  now, but *only* the genuine split: a bare ``Foo`` not followed by ``.lean``
  is left alone, because many notes cite a module bare to mean "see also that
  module" while citing declarations from elsewhere.  Accepting those too took
  the report from 72 findings to 523 and destroyed its signal.

* **Bare ``end`` closes the innermost open scope.**  The scanner tracks
  ``namespace``, ``section`` and both spellings of ``end``, and skips block and
  doc comments -- prose beginning a line with the word "namespace" inside a
  docstring will otherwise open a phantom namespace that is never closed.

Like the other gates this is lexical, not a Lean elaboration.
"""
from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path

FRONTIER_ROOT = Path(__file__).resolve().parent.parent
FABIUS_ROOT = FRONTIER_ROOT.parent.parent
LEAN = FABIUS_ROOT / "Lean" / "FabiusFunction"

CITE = re.compile(r"\\(?:lean|path|decl)\{([^}]*)\}")
# the same, but also capturing a ".lean" written immediately after the macro:
# the split module spelling \path{Foo}\texttt{.lean}
CITE_EXT = re.compile(r"\\(?:lean|path|decl)\{([^}]*)\}(\\texttt\{\.lean\}|\.lean)?")

BLOCK_ENVS = ("remark", "note", "proof", "definition", "theorem", "lemma",
              "proposition", "corollary", "example")
BLOCK = re.compile(
    r"\\begin\{(" + "|".join(BLOCK_ENVS) + r")\}(.*?)\\end\{\1\}", re.S)

DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'\u2080-\u2089]*)")
NS_OPEN = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.']*)")
SECTION = re.compile(r"^\s*section(?:\s+([A-Za-z_][A-Za-z0-9_.']*))?\s*$")
END = re.compile(r"^\s*end(?:\s+([A-Za-z_][A-Za-z0-9_.']*))?\s*$")

LEANNAME = re.compile(r"^[A-Za-z_][A-Za-z0-9_.'\u2080-\u2089]*$")

# Namespaces known to live outside this corpus.  Citations headed by one of
# these are reported but never failed.
EXTERNAL_HEADS = {
    "Real", "Complex", "Nat", "Int", "Rat", "Finset", "Set", "Filter", "List",
    "Polynomial", "PowerSeries", "MeasureTheory", "Mathlib", "Function",
    "Classical", "Order", "Topology", "Metric", "Asymptotics", "HasDerivAt",
    "Continuous", "Matrix", "Multiset", "Bool", "Prod", "Sigma", "Subtype",
    "BigOperators", "intervalIntegral", "Summable", "HasSum", "Antitone",
    "Monotone", "StrictMono", "StrictMonoOn", "Convex", "EuclideanSpace",
    "NNReal", "ENNReal", "Units", "Ideal", "Module", "Algebra", "RingHom",
    "MonoidHom", "AddMonoidHom", "LinearMap", "Equiv", "Quotient", "Sym",
    "Commute", "Tendsto", "Gamma", "ArithmeticFunction",
}


def corpus_symbols():
    """Return (name -> set of modules, set of namespace paths)."""
    where: dict[str, set[str]] = {}
    namespaces: set[str] = set()
    for fn in sorted(os.listdir(LEAN)):
        if not fn.endswith(".lean"):
            continue
        stack: list[tuple[str, str | None]] = []
        depth = 0
        with open(LEAN / fn, encoding="utf-8", errors="replace") as fh:
            for raw in fh:
                line = raw.rstrip("\n")
                opens, closes = line.count("/-"), line.count("-/")
                if depth:
                    depth = max(0, depth + opens - closes)
                    continue
                if opens > closes:
                    depth += opens - closes
                    continue
                m = NS_OPEN.match(line)
                if m:
                    stack.append(("ns", m.group(1)))
                    prefix = ".".join(n for k, n in stack if k == "ns" and n)
                    namespaces.add(prefix)
                    namespaces.add(prefix.split(".")[0])
                    continue
                m = SECTION.match(line)
                if m:
                    stack.append(("sec", m.group(1)))
                    continue
                if END.match(line):
                    if stack:
                        stack.pop()
                    continue
                m = DECL.match(line)
                if m:
                    prefix = ".".join(n for k, n in stack if k == "ns" and n)
                    short = m.group(1)
                    full = (prefix + "." + short) if prefix else short
                    where.setdefault(full, set()).add(fn)
                    where.setdefault(short, set()).add(fn)
    return where, namespaces


def doc_files():
    for root, _dirs, files in os.walk(FRONTIER_ROOT):
        for fn in sorted(files):
            if fn.endswith((".tex", ".md")):
                yield Path(root) / fn


def main() -> int:
    ap = argparse.ArgumentParser(description="crosswalk attribution audit")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--unchecked", action="store_true")
    ap.add_argument("--strict", action="store_true",
                    help="also fail on attribution mismatches")
    args = ap.parse_args()

    where, namespaces = corpus_symbols()
    modules = {fn for fn in os.listdir(LEAN) if fn.endswith(".lean")}

    mismatches: list[tuple[str, str, str, str]] = []
    blocks_checked = 0
    unresolved_ns: list[tuple[str, str]] = []
    unchecked: dict[str, set[str]] = {}
    checked_heads = 0

    for path in doc_files():
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        rel = str(path.relative_to(FABIUS_ROOT))

        # (A) attribution, per crosswalk block
        for m in BLOCK.finditer(text):
            body = m.group(2)
            mods: list[str] = []
            split_named: set[str] = set()
            for mm in CITE_EXT.finditer(body):
                c = mm.group(1).strip()
                if c.endswith(".lean") and c in modules:
                    mods.append(c)
                elif mm.group(2) and c + ".lean" in modules:
                    mods.append(c + ".lean")
                    split_named.add(c)
            if not mods:
                continue
            blocks_checked += 1
            for c in (c.strip() for c in CITE.findall(body)):
                if c.endswith(".lean") or c in split_named or not LEANNAME.match(c):
                    continue
                short = c.split(".")[-1]
                homes = where.get(c) or where.get(short)
                if homes is None:
                    continue            # existence is the other gate's job
                if not (homes & set(mods)):
                    mismatches.append((rel, m.group(1), c, ", ".join(sorted(homes))))

        # (B) namespace head, over every citation in the file
        for c in {c.strip() for c in CITE.findall(text)}:
            if c.endswith(".lean") or not LEANNAME.match(c) or "." not in c:
                continue
            head = c.split(".")[0]
            if head == "Fabius":
                continue                # the existing name audit owns these
            if head in EXTERNAL_HEADS:
                unchecked.setdefault(c, set()).add(rel)
                continue
            if head in namespaces:
                checked_heads += 1
                if c not in where:
                    unresolved_ns.append((rel, c))
            else:
                unchecked.setdefault(c, set()).add(rel)

    print("crosswalk blocks naming a module  : %d" % blocks_checked)
    print("attribution mismatches            : %d%s"
          % (len(mismatches), "" if args.strict else "  (reported, not failed)"))
    print("corpus-namespace citations checked: %d" % checked_heads)
    print("  of those, unresolved            : %d" % len(unresolved_ns))
    print("citations with an unknown head    : %d  (reported, never failed)"
          % len(unchecked))

    if mismatches:
        print()
        shown = mismatches if args.list else mismatches[:25]
        for rel, env, cite, homes in sorted(shown):
            print("  MISATTRIBUTED %-44s lives in %-36s [%s in %s]"
                  % (cite, homes, env, rel))
        if not args.list and len(mismatches) > 25:
            print("  ... %d more; rerun with --list" % (len(mismatches) - 25))
    for rel, cite in sorted(unresolved_ns):
        print("  UNRESOLVED    %-44s cited in %s" % (cite, rel))
    if args.unchecked:
        for cite in sorted(unchecked):
            print("  UNCHECKED     %-44s cited in %s"
                  % (cite, ", ".join(sorted(unchecked[cite]))[:90]))

    return 1 if (unresolved_ns or (args.strict and mismatches)) else 0


if __name__ == "__main__":
    sys.exit(main())
