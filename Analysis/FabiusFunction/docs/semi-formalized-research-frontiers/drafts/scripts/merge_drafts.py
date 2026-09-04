# -*- coding: utf-8 -*-
r"""Consolidate a group of draft LaTeX documents into a single volume.

Usage:  python merge_drafts.py <config.json>
with config {"group_dir": ..., "members": [[dir, main.tex], ...],
"out_name": ..., "title": ...}.  The output volume has one \part per
member, in config order, plus a generated title page, table of
contents, and a provenance section with each member's SHA-256.  The
first member's preamble is the base.  Its font setup is normalized to the
repository-wide Libertinus-prose/Computer-Modern-math policy.

Per member:
  - split preamble / body at \begin{document} ... \end{document};
  - strip \maketitle, \tableofcontents, titling commands, and member-local
    page-number resets from the body;
  - demote member-local \part / \part* headings so the generated wrapper owns
    the volume's one-part-per-member hierarchy;
  - prefix every label/ref/cite key with p<i>: to avoid collisions;
  - relocate \includegraphics/\input/\lstinputlisting/\verbatiminput
    paths into assets/<member>/, honoring the member's \graphicspath,
    and copy the member's support files there;
  - union packages and tikz libraries across ALL members up front
    (style packages excluded: fonts, encodings, geometry, headers);
    named xcolor palettes are enabled via \PassOptionsToPackage;
  - collect custom macros and setup commands (colors, theorem
    environments, tcolorboxes, operators, environments, column types);
    identical duplicates are deduplicated, true conflicts renamed
    per-part (\XPartii, environment renames rewrite \begin/\end), and
    commands provided by unioned packages at \begin{document} (e.g.
    siunitx's unit abbreviations \J, \K, ...) are pre-seeded so member
    macros of those names take the rename path.

This tool performed the 2026-08-28 one-volume-per-group consolidation
recorded in MANIFEST.md; rerun it if a group ever needs re-merging with
a newly arrived member.  Verify a rebuilt volume with three pdflatex
passes: 0 multiply-defined labels, 0 undefined references, no missing
files, and embedded Libertinus prose fonts.
"""
import re, os, io, sys, hashlib, shutil

def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()

LABEL_CMDS = ['label', 'ref', 'eqref', 'pageref', 'autoref', 'cref', 'Cref',
              'cite', 'bibitem', 'nameref']

def prefix_labels(text, pfx):
    # \cmd{key} and \cmd[opt]{key}  (bibitem may have [..])
    def rep(m):
        cmd, opt, keys = m.group(1), m.group(2) or '', m.group(3)
        newkeys = ','.join(pfx + k.strip() for k in keys.split(','))
        return '\\%s%s{%s}' % (cmd, opt, newkeys)
    pat = re.compile(r'\\(' + '|'.join(LABEL_CMDS) + r')(\[[^\]]*\])?\{([^{}]+)\}')
    text = pat.sub(rep, text)
    # \hyperref[key]{...}
    text = re.sub(r'\\hyperref\[([^\]]+)\]',
                  lambda m: '\\hyperref[%s]' % ','.join(pfx + k.strip() for k in m.group(1).split(',')),
                  text)
    return text

# commands provided by packages we may union in: a later member's
# \newcommand of one of these must take the conflict/rename path, since
# the package's definition is invisible to the macro registry
PKG_PROVIDES = {
    # siunitx v2 also defines the whole unit-abbreviation set at
    # \begin{document} (\J = joule etc.), invisible to \show in the
    # preamble — a member's \newcommand{\J} must take the rename path
    'siunitx': (
        'num si SI qty unit ang tablenum numlist numrange SIlist SIrange '
        'sisetup '
        'fg pg ng ug mg g kg amu pm nm um mm cm dm m km as fs ps ns us ms s '
        'fmol pmol nmol umol mmol mol kmol pA nA uA mA A kA mL L hL '
        'mHz Hz kHz MHz GHz THz mN N kN MN Pa kPa MPa GPa mohm kohm Mohm '
        'pV nV uV mV V kV uW mW W kW MW GW uJ mJ J kJ '
        'meV eV keV MeV GeV TeV fF pF F K dB'
    ).split(),
    'algorithm2e': ['listofalgorithms'],
    'nicefrac': ['nicefrac'],
    'xfrac': ['sfrac'],
}

def seed_pkg_macros(pkgs, all_macros):
    for pkg in pkgs:
        for nm in PKG_PROVIDES.get(pkg, []):
            all_macros.setdefault(nm, ('package', '\x00pkg:' + pkg))

def asset_paths(text, member, gpath=''):
    # gpath: the member's \graphicspath prefix (e.g. 'figures/'), applied
    # to bare file names before relocation under assets/<member>/
    def rep_g(m):
        opt, path = m.group(1) or '', m.group(2)
        if path.startswith('assets/'):
            return m.group(0)
        if gpath and '/' not in path:
            path = gpath + path
        return '\\includegraphics%s{assets/%s/%s}' % (opt, member, path)
    text = re.sub(r'\\includegraphics(\[[^\]]*\])?\{([^{}]+)\}', rep_g, text)
    def rep_i(m):
        path = m.group(1)
        if path.startswith('assets/'):
            return m.group(0)
        return '\\input{assets/%s/%s}' % (member, path)
    text = re.sub(r'\\input\{([^{}]+)\}', rep_i, text)
    def rep_l(m):
        cmd, opt, path = m.group(1), m.group(2) or '', m.group(3)
        if path.startswith('assets/'):
            return m.group(0)
        return '\\%s%s{assets/%s/%s}' % (cmd, opt, member, path)
    text = re.sub(r'\\(lstinputlisting|verbatiminput|inputminted)'
                  r'(\[[^\]]*\])?\{([^{}]+)\}', rep_l, text)
    return text

MACRO_PAT = re.compile(
    r'^[ \t]*\\(newcommand|renewcommand|providecommand)\*?\{?\\(\w+)\}?'
    r'((?:\[[^\]]*\])*)\{', re.M)

def macro_defs(preamble):
    """name -> (kind, full definition text)."""
    defs = {}
    for m in MACRO_PAT.finditer(preamble):
        kind = m.group(1)
        name = m.group(2)
        # capture balanced braces from the last { of the match
        start = m.end() - 1
        depth = 0
        i = start
        while i < len(preamble):
            if preamble[i] == '{' and (i == 0 or preamble[i-1] != '\\'):
                depth += 1
            elif preamble[i] == '}' and preamble[i-1] != '\\':
                depth -= 1
                if depth == 0:
                    break
            i += 1
        defs[name] = (kind, preamble[m.start():i+1])
    return defs

PKG_PAT = re.compile(r'^[ \t]*\\usepackage(\[[^\]]*\])?\{([^{}]+)\}', re.M)
TIKZLIB_PAT = re.compile(
    r'^[ \t]*\\(usetikzlibrary|usepgfplotslibrary)\{([^{}]+)\}', re.M)

def package_names(preamble):
    out = {}
    for m in PKG_PAT.finditer(preamble):
        opts = m.group(1) or ''
        for name in m.group(2).split(','):
            out[name.strip()] = opts
    return out

def tikz_libraries(preamble):
    out = {}
    for m in TIKZLIB_PAT.finditer(preamble):
        for name in m.group(2).split(','):
            out[(m.group(1), name.strip())] = True
    return out

SETUP_PAT = re.compile(
    r'^[ \t]*\\(definecolor|colorlet|newtheorem\*?|DeclareMathOperator\*?|'
    r'lstdefinestyle|newtcolorbox|newtcbox|crefname|Crefname|theoremstyle|'
    r'newenvironment\*?|newcolumntype)'
    r'\{([^{}]*)\}', re.M)

def setup_defs(preamble):
    """Ordered list of (kind, name, full text) for preamble setup commands."""
    out = []
    lines = preamble.split('\n')
    for m in SETUP_PAT.finditer(preamble):
        kind = m.group(1).rstrip('*')
        name = m.group(2)
        # balanced capture from match start to the point where braces close
        i = m.start()
        depth = 0
        seen = False
        while i < len(preamble):
            c = preamble[i]
            if c == '{' and preamble[i-1] != '\\':
                depth += 1
                seen = True
            elif c == '}' and preamble[i-1] != '\\':
                depth -= 1
            elif c == '\n' and seen and depth == 0:
                if kind == 'newenvironment':
                    # begin/end bodies may sit on following lines
                    j = i + 1
                    while j < len(preamble) and preamble[j] in ' \t':
                        j += 1
                    if j < len(preamble) and preamble[j] in '{[':
                        i += 1
                        continue
                break
            i += 1
        out.append((kind, name, preamble[m.start():i].rstrip()))
    return out

def split_doc(tex):
    m = re.search(r'\\begin\{document\}', tex)
    e = re.search(r'\\end\{document\}', tex)
    if not m or not e:
        raise RuntimeError('no document environment')
    return tex[:m.start()], tex[m.end():e.start()]

def strip_titling(body):
    body = re.sub(r'\\maketitle', '', body)
    body = re.sub(r'\\tableofcontents', '', body)
    body = re.sub(r'\\begin\{titlepage\}.*?\\end\{titlepage\}', '', body, flags=re.S)
    # A member may switch from roman front matter back to arabic page one.
    # In a collected volume those commands duplicate page anchors and make
    # the printed pagination jump backwards, so the wrapper owns pagination.
    body = re.sub(r'\\pagenumbering\{[^{}]+\}', '', body)
    body = re.sub(r'\\setcounter\{page\}\{[^{}]+\}', '', body)
    return body

PART_LINE_PAT = re.compile(r'^([ \t]*)\\part(\*?)(?![A-Za-z@])', re.M)
PROTECTED_BODY_PAT = re.compile(
    r'\\begin\{(verbatim\*?|Verbatim\*?|BVerbatim|LVerbatim|SaveVerbatim|'
    r'lstlisting|minted|alltt|comment)\}'
    r'.*?\\end\{\1\}', re.S)

def demote_member_parts(text):
    """Demote member-local part headings without rewriting literal examples."""
    out, pos = [], 0
    for match in PROTECTED_BODY_PAT.finditer(text):
        out.append(PART_LINE_PAT.sub(r'\1\\section\2', text[pos:match.start()]))
        out.append(match.group(0))
        pos = match.end()
    out.append(PART_LINE_PAT.sub(r'\1\\section\2', text[pos:]))
    return ''.join(out)

def extract_title(pre):
    # A PDF title commonly contains commas.  Stopping at the first comma made
    # wrapper titles such as "Gamma Duality, Total Positivity, ..." collapse
    # to their first phrase.
    m = re.search(r'pdftitle\s*=\s*\{((?:[^{}]|\{[^{}]*\})*)\}', pre)
    if m:
        return m.group(1).strip()
    m = re.search(r'\\title\{(.+?)\}\s*$', pre, re.S | re.M)
    if m:
        t = re.sub(r'\\\\\[[^\]]*\]', ' ', m.group(1))
        t = re.sub(r'\\(bfseries|color\{\w+\}|textbf)\s*', '', t)
        return re.sub(r'[{}]', '', t).strip()[:120]
    return None

FONT_PACKAGES = {
    'lmodern', 'libertinus', 'libertine', 'libertinust1math',
    'newtxtext', 'newtxmath', 'newtx', 'newpxtext', 'newpxmath',
    'mathpazo', 'times', 'txfonts', 'pxfonts', 'kpfonts', 'fourier',
    'fontspec',
}

def normalize_base_fonts(preamble):
    """Use Libertinus prose and leave the existing Computer Modern math."""
    def keep_nonfont_packages(m):
        opts = m.group(1) or ''
        names = [name.strip() for name in m.group(2).split(',')]
        kept = [name for name in names if name not in FONT_PACKAGES]
        if not kept:
            return ''
        return '\\usepackage%s{%s}' % (opts, ','.join(kept))
    preamble = PKG_PAT.sub(keep_nonfont_packages, preamble)
    font_line = ('\\IfFileExists{libertinus.sty}'
                 '{\\usepackage{libertinus}}{\\usepackage{lmodern}}')
    anchor = re.search(
        r'^\s*\\usepackage(?:\[[^\]]*\])?\{(?:inputenc|fontenc)\}\s*$',
        preamble, re.M)
    if anchor:
        return preamble[:anchor.end()] + '\n' + font_line + preamble[anchor.end():]
    dc = re.search(r'^\\documentclass[^\n]*$', preamble, re.M)
    if not dc:
        raise RuntimeError('base preamble has no documentclass')
    return preamble[:dc.end()] + '\n' + font_line + preamble[dc.end():]

def consolidate(group_dir, members, out_name, title, out_subdir=None):
    out_dir = os.path.join(group_dir, out_subdir or out_name)
    os.makedirs(os.path.join(out_dir, 'assets'), exist_ok=True)
    base_pre = None
    parts = []
    all_macros = {}
    provenance = []
    # pre-pass: union packages and tikz libraries across ALL members up
    # front — a package loads in the preamble, i.e. before every member's
    # body extras, so its commands must exist (and be registered) before
    # any member's body emits a \newcommand of the same name
    # only packages that would override the base document's global
    # style; functional packages (hyperref, cleveref, ...) are safe to
    # union because the `name not in all_pkgs` check already prevents
    # double-loading with clashing options
    PKG_BLOCK = {
        'lmodern', 'libertinus', 'libertine', 'libertinust1math', 'newtxtext',
        'newtxmath', 'newtx', 'newpxtext', 'newpxmath', 'mathpazo',
        'times', 'txfonts', 'pxfonts', 'kpfonts', 'fourier',
        'fontspec', 'inputenc', 'fontenc', 'babel', 'geometry',
        'fancyhdr', 'titlesec', 'titling', 'sectsty'}
    all_pkgs = None
    all_tikz = None
    extra_pkgs = []
    for mdir, mtex in members:
        mpre = split_doc(io.open(os.path.join(group_dir, mdir, mtex),
                                 encoding='utf-8').read())[0]
        if all_pkgs is None:
            all_pkgs = package_names(mpre)
            all_tikz = tikz_libraries(mpre)
            base_defs = macro_defs(mpre)
            continue
        for name, opts in package_names(mpre).items():
            if name not in all_pkgs and name not in PKG_BLOCK:
                all_pkgs[name] = opts
                extra_pkgs.append('\\usepackage%s{%s}' % (opts, name))
                clash = set(PKG_PROVIDES.get(name, ())) & set(base_defs)
                if clash:
                    print('WARNING: unioned package %s provides %s, '
                          'already macros of the base member' %
                          (name, sorted(clash)))
        for key in tikz_libraries(mpre):
            if key not in all_tikz:
                all_tikz[key] = True
                extra_pkgs.append('\\%s{%s}' % key)
    for i, (mdir, mtex) in enumerate(members, 1):
        pfx = 'p%d:' % i
        path = os.path.join(group_dir, mdir, mtex)
        tex = io.open(path, encoding='utf-8').read()
        pre, body = split_doc(tex)
        provenance.append((mdir, mtex, sha256(path), extract_title(pre) or mdir))
        body = strip_titling(body)
        body = demote_member_parts(body)
        body = prefix_labels(body, pfx)
        gm = re.search(r'\\graphicspath\{+([^{}]*?)/?\}+', pre)
        gpath = (gm.group(1).strip() + '/') if gm and gm.group(1).strip() else ''
        body = asset_paths(body, mdir, gpath)
        if base_pre is None:
            base_pre = pre
            all_macros = macro_defs(pre)
            all_setup = {(k, n): re.sub(r'\s+', '', t)
                         for k, n, t in setup_defs(pre)}
            for k, n, txt in setup_defs(pre):
                if k == 'DeclareMathOperator':
                    all_macros.setdefault(n.lstrip('\\'),
                                          ('newcommand', txt))
            env_kinds = {'newtheorem', 'newtcolorbox', 'newenvironment'}
            env_names = {n for k, n, _ in setup_defs(pre) if k in env_kinds}
            seed_pkg_macros(all_pkgs, all_macros)
            renames = {}
        else:
            defs = macro_defs(pre)
            renames = {}
            env_renames = {}
            extra = []
            for name, (kind, d) in defs.items():
                if name in all_macros or name in env_names:
                    if name in all_macros:
                        okind, od = all_macros[name]
                        if re.sub(r'\s+', '', od) == re.sub(r'\s+', '', d):
                            continue  # identical, dedupe
                        if kind == 'renewcommand':
                            extra.append(d)  # reconfigures a package macro
                            continue
                    newname = '%sPart%s' % (name, 'ivxlc'[i % 5] * (1 + i // 5))
                    renames[name] = newname
                    # a TeX control word ends at any non-letter, so use a
                    # letter lookahead, not \b (which treats _ as a word char)
                    extra.append(re.sub(r'\\' + name + r'(?![A-Za-z])',
                                        r'\\' + newname, d, count=1))
                else:
                    all_macros[name] = (kind, d)
                    extra.append(d)
            for old, new in renames.items():
                body = re.sub(r'\\' + old + r'(?![A-Za-z])', r'\\' + new, body)
            reexecutable = {'definecolor', 'colorlet', 'lstdefinestyle',
                            'crefname', 'Crefname'}
            for k, n, txt in setup_defs(pre):
                key = (k, n)
                norm = re.sub(r'\s+', '', txt)
                if key in all_setup:
                    if all_setup[key] == norm:
                        continue
                    if k in reexecutable:
                        extra.append(txt)  # re-executes, reconfiguring
                    elif k in env_kinds:
                        # A same-kind conflict can still change meaning: one
                        # report may caption `problem` as "Open problem" and
                        # another as "Problem".  Preserve the later member by
                        # giving its environment a part-local name.
                        newname = '%sPart%s' % (
                            n, 'ivxlc'[i % 5] * (1 + i // 5))
                        env_renames[n] = newname
                        txt2 = txt.replace('{%s}' % n, '{%s}' % newname, 1)
                        all_setup[(k, newname)] = re.sub(r'\s+', '', txt2)
                        env_names.add(newname)
                        extra.append(txt2)
                    continue  # non-reexecutable duplicates: keep first
                if k in env_kinds and (n in env_names or n in all_macros):
                    # name taken by another kind (or by a macro): rename
                    # the environment per-part and rewrite its uses
                    newname = '%sPart%s' % (n, 'ivxlc'[i % 5] * (1 + i // 5))
                    env_renames[n] = newname
                    txt2 = txt.replace('{%s}' % n, '{%s}' % newname, 1)
                    all_setup[(k, newname)] = re.sub(r'\s+', '', txt2)
                    env_names.add(newname)
                    extra.append(txt2)
                    continue
                all_setup[key] = norm
                if k in env_kinds:
                    env_names.add(n)
                if k == 'theoremstyle':
                    continue  # only meaningful adjacent to its newtheorem
                if k == 'DeclareMathOperator':
                    # preamble-only: convert to \newcommand + \operatorname
                    mm = re.match(
                        r'\\DeclareMathOperator(\*?)\{(\\\w+)\}\{(.*)\}\s*$',
                        txt, re.S)
                    if mm:
                        star, cmd, opname = mm.groups()
                        bare = cmd.lstrip('\\')
                        if bare in all_macros:
                            continue  # a macro of this name already exists
                        txt = '\\newcommand{%s}{\\operatorname%s{%s}}' % (
                            cmd, star, opname)
                        all_macros[bare] = ('newcommand', txt)
                extra.append(txt)
            for old, new in env_renames.items():
                body = re.sub(r'\\begin\{' + old + r'\}',
                              '\\\\begin{' + new + '}', body)
                body = re.sub(r'\\end\{' + old + r'\}',
                              '\\\\end{' + new + '}', body)
            if extra:
                parts.append('%% extra macros for part %d\n' % i + '\n'.join(extra) + '\n')
        parts.append('\\clearpage\n\\part{%s}\n'
                     '\\setcounter{section}{0}\n'
                     '\\renewcommand{\\thesection}{\\arabic{section}}\n'
                     '%% Absorbed from %s/%s\n' % (
            provenance[-1][3].replace('&', '\\&'), mdir, mtex))
        parts.append(body)
        # move assets
        srcdir = os.path.join(group_dir, mdir)
        dstdir = os.path.join(out_dir, 'assets', mdir)
        os.makedirs(dstdir, exist_ok=True)
        for root, dirs, files in os.walk(srcdir):
            rel = os.path.relpath(root, srcdir)
            for fn in files:
                if fn == mtex and rel == '.':
                    continue  # the merged source itself
                if fn.lower().endswith('.pdf') and os.path.splitext(fn)[0].lower() == os.path.splitext(mtex)[0].lower() and rel == '.':
                    continue  # the member's own compiled PDF
                d = os.path.join(dstdir, rel)
                os.makedirs(d, exist_ok=True)
                src = os.path.join(root, fn)
                dst = os.path.join(d, fn)
                if fn in ('SHA256SUMS', 'SHA256SUMS.txt'):
                    # Package checksum manifests are retired repository-wide;
                    # consolidation must not copy or regenerate them.
                    continue
                elif fn.lower().endswith('.tex'):
                    frag = io.open(src, encoding='utf-8').read()
                    frag = prefix_labels(frag, pfx)
                    frag = asset_paths(frag, mdir)
                    io.open(dst, 'w', encoding='utf-8', newline='\n').write(frag)
                else:
                    shutil.copy2(src, dst)
    prov_lines = '\n'.join(
        '\\item \\path{%s/%s} \\\\ {\\footnotesize SHA-256 \\path{%s}}' % (d, t, s)
        for d, t, s, _ in provenance)
    banner = ('\\section*{Provenance}\n'
              'This volume consolidates the following drafts verbatim (labels, citation keys, and\n'
              'asset paths mechanically prefixed per part; no mathematical content altered).\n'
              'The absorbed drafts are deleted from the working tree; git history is the archive.\n'
              '\\begin{itemize}\n' + prov_lines + '\n\\end{itemize}\n\\clearpage\n')
    newtitle = ('\\title{\\bfseries %s}\n\\author{}\n'
                '\\date{Consolidated 28 August 2026}\n' % title)
    base_pre = normalize_base_fonts(base_pre)
    # Member counter resets (especially `\appendix`) can otherwise reuse PDF
    # destination names across parts. Members may also want xcolor's named
    # palettes while the base loads xcolor optionless; pass both options before
    # either package is loaded.
    base_pre = re.sub(r'(\\documentclass[^\n]*\n)',
                      '\\g<1>\\\\PassOptionsToPackage'
                      '{hypertexnames=false}{hyperref}\n'
                      '\\\\PassOptionsToPackage'
                      '{dvipsnames,svgnames}{xcolor}\n',
                      base_pre, count=1)
    pdf_metadata = (
        '\\hypersetup{pdftitle={%s},pdfauthor={},'
        'pdfsubject={Consolidated Fabius--Rvachev research frontiers}}\n' % title
        if 'hyperref' in all_pkgs else '')
    out = (base_pre + '\n'.join(extra_pkgs) + '\n' + pdf_metadata +
           newtitle + '\\begin{document}\n\\maketitle\n\\tableofcontents\n\\clearpage\n'
           + banner + '\n'.join(parts) + '\n\\end{document}\n')
    io.open(os.path.join(out_dir, out_name + '.tex'), 'w', encoding='utf-8', newline='\n').write(out)
    print('wrote', os.path.join(out_dir, out_name + '.tex'))
    return out_dir

if __name__ == '__main__':
    import json
    cfg = json.load(open(sys.argv[1], encoding='utf-8'))
    consolidate(cfg['group_dir'], [tuple(m) for m in cfg['members']],
                cfg['out_name'], cfg['title'], cfg.get('out_subdir'))
