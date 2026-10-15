"""Apply shortening linter suggestions from lint_pass.py output.

usage: python -X utf8 apply_lint.py LINTDIR MODULE [MODULE ...]
Handled (everything else is ignored):
  * `This simp argument is unused` -> drop the argument (and its comma; an emptied list is removed);
  * `'X' tactic does nothing` / `this tactic is never executed` -> delete the tactic when it is the
    only thing on its line (or the trailing `<;> X` / `; X` at the end of a line);
  * `try 'simp' instead of 'simpa'` -> `simpa` becomes `simp` when no `using` follows.
Edits are applied bottom-up.  Prints `module: n edits`.
"""
import re
import sys
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
W = re.compile(r'^.*?\.lean:(\d+):(\d+): warning: (.*)$')


def parse(path):
    out = []
    for l in path.read_text(encoding='utf8').splitlines():
        m = W.match(l)
        if m:
            out.append((int(m.group(1)), int(m.group(2)), m.group(3)))
    return out


def arg_end(s, i):
    depth = 0
    while i < len(s):
        c = s[i]
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            if depth == 0:
                return i
            depth -= 1
        elif c == ',' and depth == 0:
            return i
        i += 1
    return i


def drop_simp_arg(line, col):
    # line[col:] starts with the argument; it sits inside [ ... ]
    e = arg_end(line, col)
    before, after = line[:col], line[e:]
    if after.startswith(','):
        after = after[1:].lstrip(' ')
    else:
        before = re.sub(r',\s*$', '', before)
    new = before + after
    new = re.sub(r'\s*\[\s*\]', '', new)
    return new


class Edited(str):
    """A line changed by an edit."""


def tidy(lines):
    """Clean up after the edits: strip trailing blanks on changed lines, drop lines that the edits
    emptied, and pull a line that now starts with `]` up onto the previous line."""
    out = []
    for l in lines:
        if not isinstance(l, Edited):
            out.append(l)
            continue
        l = l.rstrip()
        if l.strip() == '':
            continue
        if l.lstrip().startswith(']') and out:
            prev = re.sub(r',\s*$', '', out[-1].rstrip())
            out[-1] = prev + l.lstrip()
            continue
        out.append(l)
    return out


def main():
    lintdir = Path(sys.argv[1])
    for m in sys.argv[2:]:
        f = lintdir / f'{m}.txt'
        if not f.exists():
            continue
        warns = parse(f)
        if not warns:
            continue
        p = GS / f'{m}.lean'
        lines = p.read_text(encoding='utf8').split('\n')
        edits = 0
        seen = set()
        for ln, col, msg in sorted(warns, key=lambda w: (-w[0], -w[1])):
            if (ln, col) in seen:
                continue
            i = ln - 1
            s = lines[i]
            if msg.startswith('This simp argument is unused'):
                new = drop_simp_arg(s, col)
            elif "tactic does nothing" in msg or msg.startswith('this tactic is never executed'):
                rest = s[col:].rstrip()
                head = s[:col]
                if head.strip() == '' and rest and not rest.endswith((':= by', 'by', '=>', '·')):
                    # whole line (a one-line tactic); keep lines that open blocks
                    if i + 1 < len(lines) and len(lines[i + 1]) - len(lines[i + 1].lstrip()) > col:
                        continue  # the tactic continues on the next line
                    lines.pop(i)
                    seen.add((ln, col))
                    edits += 1
                    continue
                mm = re.search(r'\s*(<;>|;)\s*$', head)
                if mm and '\n' not in rest and re.fullmatch(r"[A-Za-z_][\w.']*", rest):
                    new = head[:mm.start()]
                else:
                    continue
            elif msg.startswith("try 'simp' instead of 'simpa'"):
                if s[col:col + 5] != 'simpa' or ' using ' in s[col:]:
                    continue
                new = s[:col] + 'simp' + s[col + 5:]
            else:
                continue
            if new != s:
                lines[i] = Edited(new)
                seen.add((ln, col))
                edits += 1
        if edits:
            lines = tidy(lines)
            p.write_text('\n'.join(lines), encoding='utf8', newline='\n')
        print(f'{m}: {edits} edits', flush=True)


main()
