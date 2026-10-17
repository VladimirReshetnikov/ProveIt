"""Fold parametric copies (`…With`, `…Fejer`) into their originals.

A fold moves declarations of a copy module W into destination modules (before an anchor
declaration, or before the final `end`), replaces the proofs of printed theorems by instance
proofs, deletes W and repoints every importer of W to W's replacement imports, so that each
importer's import closure is unchanged apart from the deleted module.

API (all edits in memory until `commit()`):
    F = Fold()
    F.move(W, names, dest, anchor=None)    # anchor: declaration name in dest, or None for `end`
    F.reprove(mod, name, proof_text)       # text after `:=` (starting with ' ...' or '\n...')
    F.delete_decl(mod, name)
    F.delete_module(W, replacement)        # replacement: list of modules for W's importers
    F.doc_append(mod, text)                # appended to the first module docstring
    F.commit()                             # writes files, prints a summary
"""
import re
from pathlib import Path

import stmtx

ROOT = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b')
LEAN = ROOT / 'Combinatorics/Ramsey/Lean'
GS = LEAN / 'GowersSzemeredi'
HEAD = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?"
                  r"(theorem|lemma|def|abbrev|instance|structure|alias|inductive|class)\s+([^\s(:{\[]*)", re.M)
# a plain `/- … -/` comment at column 0 is top-level too: otherwise it would belong to the
# preceding block and vanish with it (a reproof once swallowed `/- **Gowers, Corollary 7.9.** -/`)
TOP = re.compile(r"^(?:/--|/-\s|@\[|set_option .* in$|(?:private |protected )?(?:noncomputable )?"
                 r"(?:theorem|lemma|def|abbrev|instance|structure|alias|inductive|class|attribute)\b"
                 r"|end |namespace |section|open |variable|/-!|#)", re.M)


def blocks(s):
    """Top-level declaration blocks: name -> (start, end); start includes docstring/attributes and a
    `set_option … in` prefix, end is the start of the next top-level item."""
    out = {}
    tops = sorted({m.start() for m in TOP.finditer(s)})
    for h in HEAD.finditer(s):
        name = h.group(2)
        st = h.start()
        # walk back over a docstring and `set_option … in` lines directly above
        while st > 0:
            before = s[:st]
            m = re.search(r'(?m)^set_option [^\n]* in\n\Z', before)
            if m:
                st = m.start()
                continue
            if before.endswith('-/\n'):
                j = before.rfind('/--')
                if j >= 0 and before[j:].count('-/') == 1 and (j == 0 or before[j - 1] == '\n'):
                    st = j
                    continue
            break
        nxt = [t for t in tops if t > h.end()]
        en = nxt[0] if nxt else len(s)
        # the next item may be our own continuation (e.g. a `where` line is not top-level) - fine
        out.setdefault(name, (st, en))
    return out


class Fold:
    def __init__(self):
        self.text = {}
        self.deleted = {}
        self.log = []

    def get(self, m):
        if m not in self.text:
            self.text[m] = (GS / f'{m}.lean').read_text(encoding='utf8')
        return self.text[m]

    def _block(self, m, name):
        s = self.get(m)
        b = blocks(s)
        if name not in b:
            raise KeyError(f'{name} not in {m}')
        return b[name]

    def take(self, m, name):
        s = self.get(m)
        st, en = self._block(m, name)
        blk = s[st:en].rstrip('\n') + '\n'
        self.text[m] = s[:st] + s[en:]
        return blk

    def insert(self, dest, text, anchor=None):
        s = self.get(dest)
        if anchor is None:
            i = s.rindex('\nend ') + 1
        else:
            i = self._block(dest, anchor)[0]
        self.text[dest] = s[:i] + text.rstrip('\n') + '\n\n' + s[i:]

    def move(self, src, names, dest, anchor=None):
        blk = ''.join(self.take(src, n) + '\n' for n in names)
        self.insert(dest, blk, anchor)
        self.log.append(f'moved {len(names)} from {src} to {dest}' + (f' before {anchor}' if anchor else ''))

    def reprove(self, m, name, proof):
        s = self.get(m)
        st, en = self._block(m, name)
        h = HEAD.search(s, st)
        j = stmtx.statement_end(s, h.end())
        assert 0 < j < en, (m, name)
        self.text[m] = s[:j] + ':=' + proof.rstrip('\n') + '\n\n' + s[en:].lstrip('\n')
        self.log.append(f'reproved {m}.{name}')

    def delete_decl(self, m, name):
        self.take(m, name)
        self.log.append(f'deleted {m}.{name}')

    def doc_append(self, m, text):
        s = self.get(m)
        i = s.index('/-!')
        j = s.index('-/', i)
        self.text[m] = s[:j].rstrip() + '\n\n' + text.strip() + ' -/' + s[j + 2:]

    def delete_module(self, w, replacement):
        """Delete module w. Each importer gets `replacement` in place of the import (deduplicated)."""
        s = self.get(w)
        rest = re.sub(r'(?s)/-.*?-/', '', s)
        rest = re.sub(r'(?m)^(import .*|set_option .*|noncomputable section|open .*|namespace .*|end .*|\s*)$', '', rest)
        assert not rest.strip(), f'{w} still has content: {rest.strip()[:300]}'
        self.deleted[w] = replacement
        self.log.append(f'deleted module {w} -> {replacement}')

    def _repoint(self, path, text):
        changed = False
        for w, repl in self.deleted.items():
            line = f'import GowersSzemeredi.{w}\n'
            if line not in text:
                continue
            have = set(re.findall(r'^import GowersSzemeredi\.(\S+)', text, re.M))
            me = path.stem
            new = ''.join(f'import GowersSzemeredi.{r}\n' for r in repl
                          if r not in have and r != me and r not in self.deleted)
            text = text.replace(line, new, 1)
            changed = True
        return text, changed

    def commit(self):
        for m, s in self.text.items():
            if m in self.deleted:
                continue
            s, _ = self._repoint(GS / f'{m}.lean', s)
            s = re.sub(r'\n{3,}', '\n\n', s)
            (GS / f'{m}.lean').write_text(s, encoding='utf8', newline='\n')
        # every other importer in the tree (facade, audits, …)
        touched = []
        for p in list(GS.glob('*.lean')) + list(LEAN.glob('*.lean')):
            if p.stem in self.text or p.stem in self.deleted:
                continue
            t = p.read_text(encoding='utf8')
            t2, ch = self._repoint(p, t)
            if ch:
                if p.parent == LEAN:   # the facade imports every module: just drop the line
                    t2 = t
                    for w in self.deleted:
                        t2 = t2.replace(f'import GowersSzemeredi.{w}\n', '')
                p.write_text(t2, encoding='utf8', newline='\n')
                touched.append(p.stem)
        for w in self.deleted:
            (GS / f'{w}.lean').unlink()
            for ext in ('olean', 'ilean', 'olean.private', 'olean.server', 'c', 'trace', 'hash'):
                for q in (ROOT / '.lake/build/lib/lean/GowersSzemeredi').glob(f'{w}.{ext}*'):
                    q.unlink()
        for l in self.log:
            print(l)
        print('importers repointed:', ' '.join(sorted(touched)))
