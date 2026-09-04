# -*- coding: utf-8 -*-
r"""Extend an already-consolidated LaTeX volume with further member drafts.

`merge_drafts.py` builds a volume from N peer drafts.  This variant takes an
EXISTING volume as the base and appends further members as new parts, so the
base's own part structure, label prefixes, and provenance list survive
untouched.

Design decisions specific to this merge:

  * the base body is copied verbatim -- no relabelling, no part demotion;
  * members are relabelled with prefixes continuing the base's `p<i>:` series;
  * a member's theorem environments are DROPPED, because the base already
    declares the whole shared-counter family through `\newsharedtheorem`;
    environment names the base lacks are reported so they can be added by
    hand in the base's own idiom rather than duplicated per part;
  * a member's layout preamble (colors, hypersetup, fancyhdr, lstset,
    graphicspath, titling) is dropped; only its macro definitions travel,
    deduplicated against the base and renamed on a genuine conflict.
"""
import re, os, io, sys, json, hashlib, shutil

# ---------------------------------------------------------------- utilities

def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(65536), b''):
            h.update(chunk)
    return h.hexdigest()


LABEL_CMDS = ['label', 'ref', 'eqref', 'pageref', 'autoref', 'cref', 'Cref',
              'cite', 'bibitem', 'nameref']


def prefix_labels(text, pfx):
    def rep(m):
        cmd, opt, keys = m.group(1), m.group(2) or '', m.group(3)
        newkeys = ','.join(pfx + k.strip() for k in keys.split(','))
        return '\\%s%s{%s}' % (cmd, opt, newkeys)
    pat = re.compile(r'\\(' + '|'.join(LABEL_CMDS) + r')(\[[^\]]*\])?\{([^{}]+)\}')
    text = pat.sub(rep, text)
    text = re.sub(r'\\hyperref\[([^\]]+)\]',
                  lambda m: '\\hyperref[%s]' % ','.join(
                      pfx + k.strip() for k in m.group(1).split(',')),
                  text)
    return text


def asset_paths(text, member, gpath=''):
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
    defs = {}
    for m in MACRO_PAT.finditer(preamble):
        kind, name = m.group(1), m.group(2)
        start = m.end() - 1
        depth, i = 0, start
        while i < len(preamble):
            if preamble[i] == '{' and preamble[i - 1] != '\\':
                depth += 1
            elif preamble[i] == '}' and preamble[i - 1] != '\\':
                depth -= 1
                if depth == 0:
                    break
            i += 1
        defs[name] = (kind, preamble[m.start():i + 1])
    return defs


OPERATOR_PAT = re.compile(
    r'^[ \t]*\\DeclareMathOperator(\*?)\{\\(\w+)\}\{([^{}]*)\}[ \t]*$', re.M)

PKG_PAT = re.compile(r'^[ \t]*\\usepackage(\[[^\]]*\])?\{([^{}]+)\}', re.M)
NEWTHEOREM_PAT = re.compile(
    r'^[ \t]*\\newtheorem\*?\{(\w+)\}(?:\[\w+\])?\{([^{}]*)\}', re.M)
NEWENV_PAT = re.compile(r'^[ \t]*\\newenvironment\*?\{(\w+)\}', re.M)


def package_names(preamble):
    out = {}
    for m in PKG_PAT.finditer(preamble):
        opts = m.group(1) or ''
        for name in m.group(2).split(','):
            out[name.strip()] = opts
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
    body = re.sub(r'\\pagenumbering\{[^{}]+\}', '', body)
    body = re.sub(r'\\setcounter\{page\}\{[^{}]+\}', '', body)
    body = re.sub(r'^[ \t]*\\thispagestyle\{[^{}]+\}[ \t]*\n', '', body, flags=re.M)
    return body


PART_LINE_PAT = re.compile(r'^([ \t]*)\\part(\*?)(?![A-Za-z@])', re.M)
PROTECTED_BODY_PAT = re.compile(
    r'\\begin\{(verbatim\*?|Verbatim\*?|lstlisting|minted|alltt|comment)\}'
    r'.*?\\end\{\1\}', re.S)


def demote_member_parts(text):
    out, pos = [], 0
    for match in PROTECTED_BODY_PAT.finditer(text):
        out.append(PART_LINE_PAT.sub(r'\1\\section\2', text[pos:match.start()]))
        out.append(match.group(0))
        pos = match.end()
    out.append(PART_LINE_PAT.sub(r'\1\\section\2', text[pos:]))
    return ''.join(out)


PKG_BLOCK = {
    'lmodern', 'libertinus', 'libertine', 'libertinust1math', 'newtxtext',
    'newtxmath', 'newtx', 'newpxtext', 'newpxmath', 'mathpazo', 'times',
    'txfonts', 'pxfonts', 'kpfonts', 'fourier', 'fontspec', 'inputenc',
    'fontenc', 'babel', 'geometry', 'fancyhdr', 'titlesec', 'titling',
    'sectsty', 'hyperref', 'cleveref', 'microtype', 'setspace',
}

PART_ROMAN = ['0', 'I', 'II', 'III', 'IV', 'V', 'VI', 'VII', 'VIII', 'IX',
              'X', 'XI', 'XII', 'XIII', 'XIV', 'XV']


def build(cfg):
    group_dir = cfg['group_dir']
    out_dir = os.path.join(group_dir, cfg['out_dir'])
    os.makedirs(os.path.join(out_dir, 'assets'), exist_ok=True)

    base_dir, base_tex = cfg['base']
    base_path = os.path.join(group_dir, base_dir, base_tex)
    base_all = io.open(base_path, encoding='utf-8').read()
    base_pre, base_body = split_doc(base_all)

    # Macros defined anywhere in the base are global by the time the appended
    # parts are typeset, so the body's own per-part macro blocks count too.
    base_macros = macro_defs(base_pre)
    for name, d in macro_defs(base_body).items():
        base_macros.setdefault(name, d)
    for m in OPERATOR_PAT.finditer(base_all):
        base_macros.setdefault(m.group(2), ('operator', m.group(0)))
    # Definitions the config injects into the preamble are global too.
    for name, d in macro_defs(cfg.get('preamble_extra', '')).items():
        base_macros.setdefault(name, d)
    env_scan = base_all + '\n' + cfg.get('preamble_extra', '')
    base_env_names = {n for n, _ in NEWTHEOREM_PAT.findall(env_scan)}
    base_env_names |= set(NEWENV_PAT.findall(env_scan))
    # the base declares its shared-counter family through a helper macro
    for m in re.finditer(r'\\newsharedtheorem\{(\w+)\}\{([^{}]*)\}', env_scan):
        base_env_names.add(m.group(1))
    base_pkgs = package_names(base_pre)

    # ---- the base body keeps everything after its own provenance block
    prov = re.search(r'\\section\*\{Provenance\}.*?\\end\{itemize\}\s*\\clearpage',
                     base_body, re.S)
    if not prov:
        raise RuntimeError('base provenance block not found')
    base_prov_items = re.search(r'\\begin\{itemize\}(.*?)\\end\{itemize\}',
                                prov.group(0), re.S).group(1).strip()
    base_body_parts = base_body[prov.end():]
    base_body_parts = strip_titling(base_body_parts)

    extra_pkgs, extra_macros, notes = [], [], []
    member_blocks, provenance = [], []

    for idx, member in enumerate(cfg['members']):
        mdir = member['dir']
        mtex = member['tex']
        part_title = member['part_title']
        note = member['note']
        drop = set(member.get('drop_macros', []))
        forced = dict(member.get('rename_macros', {}))
        pnum = cfg['first_prefix'] + idx
        pfx = 'p%d:' % pnum
        path = os.path.join(group_dir, mdir, mtex)
        tex = io.open(path, encoding='utf-8').read()
        pre, body = split_doc(tex)
        provenance.append((mdir, mtex, sha256(path), note))

        for name, opts in package_names(pre).items():
            if name not in base_pkgs and name not in PKG_BLOCK:
                base_pkgs[name] = opts
                extra_pkgs.append('\\usepackage%s{%s}' % (opts, name))

        for env, caption in NEWTHEOREM_PAT.findall(pre):
            if env not in base_env_names:
                notes.append('MISSING THEOREM ENV: %s -> %r (member %s)'
                             % (env, caption, mdir))
        for env in NEWENV_PAT.findall(pre):
            if env not in base_env_names:
                notes.append('MISSING ENVIRONMENT: %s (member %s)' % (env, mdir))
            else:
                notes.append('ENVIRONMENT REDEFINED BY MEMBER: %s (member %s) '
                             '-- check arity at every use' % (env, mdir))

        renames, member_macros = {}, []
        for name, (kind, d) in macro_defs(pre).items():
            norm = re.sub(r'\s+', '', d)
            if name in drop:
                notes.append('MACRO DROPPED BY CONFIG: \\%s (member %s)'
                             % (name, mdir))
                continue
            if name in forced:
                newname = forced[name]
                renames[name] = newname
                member_macros.append(
                    re.sub(r'\\' + name + r'(?![A-Za-z])',
                           r'\\' + newname, d, count=1))
                base_macros[newname] = (kind, d)
                notes.append('MACRO RENAMED BY CONFIG: \\%s -> \\%s (member %s)'
                             % (name, newname, mdir))
                continue
            if name in base_macros:
                if re.sub(r'\s+', '', base_macros[name][1]) == norm:
                    notes.append('MACRO DEDUPED: \\%s (member %s)' % (name, mdir))
                    continue
                if kind == 'renewcommand':
                    notes.append('MEMBER RENEWCOMMAND DROPPED: \\%s (member %s)'
                                 % (name, mdir))
                    continue
                newname = '%sPart%s' % (name, PART_ROMAN[pnum])
                renames[name] = newname
                member_macros.append(
                    re.sub(r'\\' + name + r'(?![A-Za-z])',
                           r'\\' + newname, d, count=1))
                base_macros[newname] = (kind, d)
                notes.append('MACRO AUTO-RENAMED (CONFLICT): \\%s -> \\%s (member %s)'
                             % (name, newname, mdir))
            else:
                base_macros[name] = (kind, d)
                member_macros.append(d)
        for m in OPERATOR_PAT.finditer(pre):
            name = m.group(2)
            if name in base_macros or name in drop:
                continue
            base_macros[name] = ('operator', m.group(0))
            member_macros.append('\\newcommand{\\%s}{\\operatorname%s{%s}}'
                                 % (name, m.group(1), m.group(3)))
        for old, new in renames.items():
            body = re.sub(r'\\' + old + r'(?![A-Za-z])', r'\\' + new, body)

        body = strip_titling(body)
        body = demote_member_parts(body)
        body = prefix_labels(body, pfx)
        gm = re.search(r'\\graphicspath\{+([^{}]*?)/?\}+', pre)
        gpath = (gm.group(1).strip() + '/') if gm and gm.group(1).strip() else ''
        body = asset_paths(body, mdir, gpath)

        rule = '% ' + '-' * 66 + '\n'
        member_macros = list(member.get('extra_macros', [])) + member_macros
        macro_block = ''
        if member_macros:
            macro_block = ('%% ed.: macros carried over with Part~%s\n'
                           % PART_ROMAN[pnum]) + '\n'.join(member_macros) + '\n'
        header = ('\n\\clearpage\n' + rule
                  + '%% Part %s -- absorbed from %s/%s\n'
                  % (PART_ROMAN[pnum], mdir, mtex)
                  + rule + macro_block
                  + '\\setcounter{section}{0}\n'
                  '\\renewcommand{\\thesection}{\\arabic{section}}\n'
                  + '\\part{%s}\n' % part_title)
        member_blocks.append(header + body)

        # ---- assets
        srcdir = os.path.join(group_dir, mdir)
        dstdir = os.path.join(out_dir, 'assets', mdir)
        os.makedirs(dstdir, exist_ok=True)
        for root, dirs, files in os.walk(srcdir):
            rel = os.path.relpath(root, srcdir)
            for fn in files:
                if rel == '.' and fn == mtex:
                    continue
                if (rel == '.' and fn.lower().endswith('.pdf')
                        and os.path.splitext(fn)[0].lower()
                        == os.path.splitext(mtex)[0].lower()):
                    continue
                d = os.path.join(dstdir, rel)
                os.makedirs(d, exist_ok=True)
                src, dst = os.path.join(root, fn), os.path.join(d, fn)
                if fn.lower().endswith('.tex'):
                    frag = io.open(src, encoding='utf-8').read()
                    frag = prefix_labels(frag, pfx)
                    frag = asset_paths(frag, mdir)
                    io.open(dst, 'w', encoding='utf-8', newline='\n').write(frag)
                else:
                    shutil.copy2(src, dst)

    # ---- reassemble
    new_prov_items = '\n'.join(
        '\\item \\path{%s/%s} \\\\ {\\footnotesize SHA-256 \\path{%s}} (%s)'
        % (d, t, s, n) for d, t, s, n in provenance)

    banner = (
        '\\section*{Provenance}\n'
        '\\label{sec:provenance}\n'
        + cfg['provenance_intro'] + '\n\n'
        '\\subsection*{Sources absorbed into Parts~I--VII}\n'
        '\\begin{itemize}\n' + base_prov_items + '\n\\end{itemize}\n'
        '\n\\subsection*{Sources absorbed in the present consolidation}\n'
        '\\begin{itemize}\n' + new_prov_items + '\n\\end{itemize}\n'
        '\\clearpage\n')

    pre = base_pre
    if extra_pkgs:
        pre = pre.rstrip() + '\n\n%% ed.: packages unioned from the absorbed members\n' \
            + '\n'.join(sorted(set(extra_pkgs))) + '\n'
    if cfg.get('preamble_extra'):
        pre = pre.rstrip() + '\n\n' + cfg['preamble_extra'] + '\n'
    pre = re.sub(r'\\title\{.*?\n\\author\{.*?\n\\date\{.*?\n(?=\\)', '', pre, flags=re.S)
    pre = pre.rstrip() + '\n\n' + cfg['titleblock'] + '\n'
    pre = re.sub(r'pdftitle=\{[^{}]*\}', 'pdftitle={%s}' % cfg['pdftitle'], pre)
    pre = re.sub(r'pdfsubject=\{[^{}]*\}', 'pdfsubject={%s}' % cfg['pdfsubject'], pre)

    out = (pre + '\\begin{document}\n\\maketitle\n\\tableofcontents\n\\clearpage\n'
           + banner + base_body_parts + ''.join(member_blocks)
           + '\n\\end{document}\n')
    outpath = os.path.join(out_dir, cfg['out_name'] + '.tex')
    io.open(outpath, 'w', encoding='utf-8', newline='\n').write(out)
    print('wrote %s  (%d lines)' % (outpath, out.count('\n') + 1))
    if notes:
        print('\n-- editorial follow-ups ------------------------------------')
        for n in notes:
            print('  ' + n)
    return outpath


if __name__ == '__main__':
    build(json.load(io.open(sys.argv[1], encoding='utf-8')))
