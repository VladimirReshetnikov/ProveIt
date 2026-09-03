# -*- coding: utf-8 -*-
"""Which volume results carry no Lean crosswalk at all?

`audit_stale_claims.py` finds results whose prose says "not formalized"
while a citation sits nearby -- a contradiction.  This finds the
opposite and larger gap: results with **no citation and no disclaimer**,
which a reader cannot tell apart from formalized ones.

A result is a `theorem`/`proposition`/`lemma`/`corollary` environment.
It counts as *covered* if a Lean citation (`\\lean`, `\\leanPart`,
`\\leanPartx`) appears inside it or in the prose immediately following
it, before the next such environment -- which is where these volumes
put their crosswalk postscripts.  It counts as *disclaimed* if that
same span says something is not formalized.  Anything else is a gap.

This is advisory: a short corollary of a covered theorem may need no
citation of its own.  The point is a worklist, not a gate.

Usage:  python audit_crosswalk_coverage.py [volume.tex ...]
        with no arguments, every .tex under drafts/.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DRAFTS = os.path.normpath(os.path.join(HERE, '..', 'drafts'))

ENV = re.compile(
    r'\\begin\{(theorem|proposition|lemma|corollary)\}'
    r'(?:\[[^\]]*\])?'
    r'\s*(?:\\label(?:\[[^\]]*\])?\{([^}]*)\})?',
    re.S)
# `\path{Fabius.name}` is the Spectra and Arithmetic volume's citation form
# (that volume defines no `\lean` macro).
LEAN = re.compile(r'\\(?:lean(?:Part|Partx)?|decl)\{|\\path\{Fabius\.')
# Labels named by a cross-reference: \cref{a,b}, \Cref{a}, \ref{a}, \eqref{a}.
XREF = re.compile(r'\\(?:[cC]ref|ref|eqref)\{([^}]*)\}')
# A unit of a ledger: a paragraph, or a row of a table (ended by \\).
UNIT_SPLIT = re.compile(r'\n\s*\n|\\\\\s*\n')
ITEM_SPLIT = re.compile(r'\\item\b')
# A result environment with its body, for the placement check.
ENV_BODY = re.compile(
    r'\\begin\{(theorem|proposition|lemma|corollary)\}(.*?)\\end\{\1\}', re.S)
FORMAL_PARA = re.compile(r'\\emph\{Formal (?:version|versions|status)')
OPEN = re.compile(
    r'not formalized|unformalized|no Lean counterpart|not yet formalized'
    r'|remains open|is not proved|not proved (?:here|anywhere)'
    r'|awaiting (?:full )?(?:Lean )?formalization|analytic premises remain'
    r'|remains? (?:an )?analytic frontiers?|not yet formal\b',
    re.I)


SECTION = re.compile(r'\\(?:sub)*section\*?\{', re.M)


def spans(text):
    """Each result, paired with the rest of its (sub)section, and with
    the prose that precedes it back to the previous result or
    sectioning command.

    These volumes put one crosswalk postscript per subsection, covering
    every result in it -- so the span must run to the next sectioning
    command, not to the next result.  Cutting at the next result made
    `p1:thm:primitive-recursive` look uncited because a lemma follows it
    and the shared crosswalk lands after the lemma.

    The *preamble* handles the other convention, where a narrative
    paragraph before a theorem says "\\cref{thm} holds as \\lean{...}".
    It is credited only when it names the result's own label, so a
    postscript belonging to the previous result is never mistaken for
    coverage of the next one.
    """
    marks = [(m.start(), m.group(1), m.group(2)) for m in ENV.finditer(text)]
    cuts = [m.start() for m in SECTION.finditer(text)]
    prev_end = 0
    for start, kind, label in marks:
        stop = len(text)
        for c in cuts:
            if c > start:
                stop = c
                break
        pre_from = prev_end
        for c in cuts:
            if c < start:
                pre_from = max(pre_from, c)
        yield kind, label, text[start:stop], text[pre_from:start]
        e = text.find('\\end{%s}' % kind, start)
        prev_end = e if e >= 0 else start


def ledger(text):
    """Labels covered by a crosswalk ledger anywhere in the file.

    Some volumes crosswalk in a dedicated appendix -- a table whose rows
    pair Lean declarations with `\\Cref{...}` pointers at the results they
    formalize, or paragraphs doing the same in prose.  A result named by a
    cross-reference in any paragraph or table row that also cites Lean is
    covered, wherever that unit sits.
    """
    covered = set()
    disclaimed = set()
    # Two levels: a paragraph (or table row) sets the disclaimer context
    # for the `\item`s it contains -- "still awaiting formalization:" is
    # said once above the list, not in every item -- while each item cites
    # or names results on its own.
    paras = UNIT_SPLIT.split(text)
    # A sectioning heading such as "Human theorems still awaiting full
    # Lean formalization" governs the paragraph that follows it.
    merged = []
    carry = ''
    for para in paras:
        # A heading, or a paragraph that ends by introducing a list
        # ("... is now explicit:"), governs what follows it.
        if SECTION.match(para.strip()) or para.strip().endswith(':'):
            carry = carry + '\n' + para
            continue
        merged.append(carry + '\n' + para)
        carry = ''
    for para in merged:
        opens_para = bool(OPEN.search(para))
        for unit in ITEM_SPLIT.split(para):
            cites = bool(LEAN.search(unit))
            opens = opens_para or bool(OPEN.search(unit))
            if not (cites or opens):
                continue
            for m in XREF.finditer(unit):
                for lab in m.group(1).split(','):
                    lab = lab.strip()
                    if not lab:
                        continue
                    if cites:
                        covered.add(lab)
                    else:
                        disclaimed.add(lab)
    return covered, disclaimed


def survey(path):
    text = io.open(path, encoding='utf-8', errors='replace').read()
    covered = disclaimed = gap = 0
    gaps = []
    led, dis = ledger(text)
    for kind, label, span, pre in spans(text):
        named = label and re.search(
            r'\\[cC]?ref\{' + re.escape(label) + r'\}', pre)
        if LEAN.search(span) or (named and LEAN.search(pre)) or (label and label in led):
            covered += 1
        elif OPEN.search(span) or (label and label in dis):
            disclaimed += 1
        else:
            gap += 1
            gaps.append((kind, label or '(no label)'))
    # Total citations in the file, to separate two very different cases:
    # a volume with an INLINE crosswalk convention and gaps in it, versus
    # one that crosswalks in a dedicated section, where "0 cited" inside
    # result spans says nothing about coverage.
    total_cites = len(LEAN.findall(text))
    # Placement hygiene: a crosswalk paragraph must not sit inside the
    # result environment it describes (between \begin{theorem} and
    # \end{theorem}); that happened once when a script anchored on the
    # display inside a proposition.
    inside = []
    for m in ENV_BODY.finditer(text):
        if FORMAL_PARA.search(m.group(2)):
            lab = re.search(r'\\label\{([^}]*)\}', m.group(2))
            inside.append(lab.group(1) if lab else '(no label)')
    return covered, disclaimed, gap, gaps, total_cites, inside


def main(argv):
    if len(argv) > 1:
        paths = argv[1:]
    else:
        paths = []
        for root, _dirs, files in os.walk(DRAFTS):
            for f in files:
                if f.endswith('.tex'):
                    paths.append(os.path.join(root, f))
        paths.sort()

    total = [0, 0, 0]
    print('== crosswalk coverage of volume results ==')
    for path in paths:
        covered, disclaimed, gap, gaps, cites, inside = survey(path)
        if covered + disclaimed + gap == 0:
            continue
        if inside:
            print()
            print('%s' % os.path.relpath(path, HERE))
            for lab in inside:
                print('   MISPLACED  crosswalk paragraph inside the environment of %s' % lab)
        total[0] += covered
        total[1] += disclaimed
        total[2] += gap
        rel = os.path.relpath(path, HERE)
        print()
        print('%s' % rel)
        note = ''
        if covered == 0 and cites > 0:
            note = ('   [%d citations in the file but none inside a result '
                    'span: this volume crosswalks elsewhere, so the gap '
                    'count below is not meaningful]' % cites)
        print('   cited %d   disclaimed %d   NO POINTER %d   (file cites %d)'
              % (covered, disclaimed, gap, cites))
        if note:
            print(note)
            continue
        for kind, label in gaps[:12]:
            print('      %-12s %s' % (kind, label))
        if len(gaps) > 12:
            print('      ... and %d more' % (len(gaps) - 12))

    print()
    print('TOTAL  cited %d   disclaimed %d   NO POINTER %d'
          % (total[0], total[1], total[2]))
    print()
    print('ADVISORY.  A short corollary of a covered theorem may')
    print('legitimately carry no citation of its own.  Read before acting.')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
