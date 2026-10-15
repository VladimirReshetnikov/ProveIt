"""Classify `Variable name ... is not explicitly referenced` warnings from lint/*.txt.

For each: enclosing declaration, whether the variable is a binder of the signature, the binder
group text, and the modules calling the declaration (with heavy ones, i.e. without a local olean,
marked).  usage: unused_hyps.py LINTDIR
"""
import os
import re
import sys
from pathlib import Path

import stmtx

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
OUT = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\.lake\build\lib\lean\GowersSzemeredi')
W = re.compile(r'(Proofs\w+)\.lean:(\d+):(\d+): warning: Variable name `([^`]+)` is not explicitly referenced')
HEAD = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?(theorem|lemma|def) ([^\s(:{\[]+)", re.M)
srcs = {f.stem: f.read_text(encoding='utf8') for f in GS.glob('*.lean')}
rows = []
for f in Path(sys.argv[1]).glob('*.txt'):
    for m in W.finditer(f.read_text(encoding='utf8')):
        mod, ln, col, var = m.group(1), int(m.group(2)), int(m.group(3)), m.group(4)
        s = srcs[mod]
        off = sum(len(l) + 1 for l in s.split('\n')[:ln - 1]) + col
        heads = [h for h in HEAD.finditer(s) if h.start() <= off]
        if not heads:
            continue
        h = heads[-1]
        end = stmtx.statement_end(s, h.end())
        in_sig = h.end() <= off < end
        name = h.group(2)
        short = name.split('.')[-1]
        callers = sorted(k for k, t in srcs.items()
                         if re.search(r"(?<![\w'])" + re.escape(short) + r"(?![\w'])", t) and k != mod
                         or (k == mod and len(re.findall(r"(?<![\w'])" + re.escape(short) + r"(?![\w'])", t)) > 1))
        heavy = [c for c in callers if not (OUT / f'{c}.olean').exists()]
        private = s[h.start():h.end()].lstrip().startswith(('private', '@')) and 'private' in s[h.start():h.end()]
        rows.append((mod, ln, var, name, in_sig, private, callers, heavy))
for r in sorted(rows):
    mod, ln, var, name, in_sig, private, callers, heavy = r
    print(f"{mod}:{ln} {var:9} {'SIG ' if in_sig else 'body'} {'priv' if private else 'pub '} {name.split('.')[-1][:45]:45} "
          f"callers={len(callers)} heavy={len(heavy)}")
