"""Extract the used declarations of the T3 route into consolidated modules.

usage: python -X utf8 final_extract.py USED_NAMES OUT_JSON
Reads the source modules below, keeps the declarations named in USED_NAMES
("module name" lines), and writes, per source module in topological order,
the kept declarations inside the module's own namespace/variable context.
Prints the per-module kept/dropped counts; writes the chunks to OUT_JSON.
"""
import json
import re
import sys
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
ROOT_NS = 'LeanProofs.GowersSzemeredi'
SOURCES = [
    'Proofs18FejerEnvelopeBaseQ', 'Proofs18TightClassesFejerQ', 'Proofs18TightClassesFejerS',
    'Proofs18TightClassesFejerT', 'Proofs18FejerEnvelopeBaseW', 'Proofs18TightClassesFejerX',
    'Proofs18TightClassesFejerZ', 'Proofs18TightClassesFejerM', 'Proofs16SplitTwoTrack',
    'Proofs16SplitTwoTrackClasses', 'Proofs16UniformCoverTwoTight', 'Proofs16SplitTwoTrackClassesT3',
    'Proofs18CoverModulusFejerQ', 'Proofs18CoverDensityFejerQ', 'Proofs18CoverExponentsFejerQ',
    'Proofs18CoverModulusFejerS', 'Proofs18CoverDensityFejerS', 'Proofs18CoverExponentsFejerS',
    'Proofs18CoverModulusFejerT', 'Proofs18CoverDensityFejerT', 'Proofs18CoverExponentsFejerT',
    'Proofs18CoverModulusFejerW', 'Proofs18CoverDensityFejerW', 'Proofs18CoverExponentsFejerW',
    'Proofs18CoverModulusFejerX', 'Proofs18CoverDensityFejerX', 'Proofs18CoverExponentsFejerX',
    'Proofs18CoverModulusFejerZ', 'Proofs18CoverDensityFejerZ', 'Proofs18CoverExponentsFejerZ',
    'Proofs18CoverModulusFejerJ', 'Proofs18CoverDensityFejerJ', 'Proofs18CoverExponentsFejerJ',
    'Proofs18CoverModulusFejerJT3', 'Proofs18CoverDensityFejerJT3', 'Proofs18CoverExponentsFejerJT3',
    'Proofs18CoverFejerHeadlineQ', 'Proofs18CoverFejerHeadlineS', 'Proofs18CoverFejerHeadlineT',
    'Proofs18CoverFejerHeadlineU', 'Proofs18CoverFejerHeadlineW', 'Proofs18CoverFejerHeadlineX',
    'Proofs18CoverFejerHeadlineZ', 'Proofs18CoverFejerHeadlineY', 'Proofs18CoverFejerHeadlineJ',
    'Proofs18CoverFejerHeadlineK', 'Proofs18CoverFejerHeadlineK3',
    'Proofs16PolynomialFejerQ', 'Proofs16PolynomialFejerS', 'Proofs16PolynomialFejerX',
    'Proofs16PolynomialFejerJ', 'Proofs16PolynomialFejerT3',
    'Proofs18CoverFejerLowDegrees5', 'Proofs18CoverFejerLowDegrees4', 'Proofs18CoverFejerShortLengths3',
]
DECL = re.compile(r'^(?:private |protected |noncomputable |nonrec )*'
                  r'(theorem|lemma|def|abbrev|structure|instance|class|inductive)\s+([^\s(:{\[]+)')
CTX = re.compile(r'^(namespace|end|section|variable|open|omit|include)\b')
HEADER = re.compile(r'^(import|set_option autoImplicit|noncomputable section|open scoped BigOperators)')


def parse(text):
    """Items: ('ctx', text) | ('decl', fullname, text) | ('drop', text)."""
    lines = text.split('\n')
    items, ns, i = [], [], 0
    pending = []  # doc comment / attribute lines waiting for their declaration
    while i < len(lines):
        line = lines[i]
        if not line.strip():
            i += 1
            continue
        if line.startswith('/-!'):
            j = i
            while '-/' not in lines[j]:
                j += 1
            items.append(('drop', '\n'.join(lines[i:j + 1])))
            i = j + 1
            continue
        if line.startswith('/--'):
            j = i
            while '-/' not in lines[j]:
                j += 1
            pending = lines[i:j + 1]
            i = j + 1
            continue
        if line.startswith('@['):
            pending.append(line)
            i += 1
            continue
        if HEADER.match(line):
            i += 1
            continue
        m = CTX.match(line)
        if m:
            kw = m.group(1)
            parts = line.split()
            if kw == 'namespace':
                ns.append(('ns', parts[1]))
            elif kw == 'section':
                ns.append(('sec', parts[1] if len(parts) > 1 else ''))
            elif kw == 'end':
                ns.pop()
            if kw == 'namespace' and parts[1] == ROOT_NS or kw == 'end' and line.strip() == f'end {ROOT_NS}':
                i += 1
                continue
            j = i + 1
            while j < len(lines) and lines[j].startswith((' ', '\t')):
                j += 1
            items.append(('ctx', '\n'.join(lines[i:j])))
            i = j
            continue
        m = DECL.match(line)
        if not m:
            raise SystemExit(f'unrecognised column-0 line {i + 1}: {line!r}')
        j = i + 1
        while j < len(lines) and (not lines[j].strip() or lines[j].startswith((' ', '\t'))
                                  or lines[j].startswith(('termination_by', 'decreasing_by'))):
            j += 1
        while j > i + 1 and not lines[j - 1].strip():
            j -= 1
        scope = [n for k, n in ns if k == 'ns' and n != ROOT_NS]
        name = '.'.join(scope + [m.group(2)])
        items.append(('decl', name, '\n'.join(pending + lines[i:j])))
        pending = []
        i = j
    return items


def prune(chunk):
    """Drop namespace/section frames and `variable` lines that frame nothing."""
    out = []
    for kind, text in chunk:
        out.append((kind, text))
        changed = True
        while changed:
            changed = False
            # a frame opened and closed with only ctx lines (variable/open) in between
            if out and out[-1][0] == 'ctx' and out[-1][1].startswith('end '):
                k = len(out) - 2
                while k >= 0 and out[k][0] == 'ctx' and out[k][1].startswith(('variable', 'open', 'omit', 'include')):
                    k -= 1
                if k >= 0 and out[k][0] == 'ctx' and out[k][1].split()[0] in ('namespace', 'section'):
                    del out[k:]
                    changed = True
    # trailing variable lines
    while out and out[-1][0] == 'ctx' and out[-1][1].startswith('variable'):
        out.pop()
    return out


def main():
    used = {}
    for l in open(sys.argv[1], encoding='utf8'):
        if l.strip():
            mod, name = l.split()
            used.setdefault(mod.split('.', 1)[1], set()).add(name.replace(ROOT_NS + '.', ''))
    chunks = {}
    total_kept = total_lines = 0
    for mod in SOURCES:
        text = (GS / f'{mod}.lean').read_text(encoding='utf8')
        total_lines += text.count('\n')
        keep = used.get(mod, set())
        chunk, kept, names = [], 0, []
        for it in parse(text):
            if it[0] == 'ctx':
                chunk.append(('ctx', it[1]))
            elif it[0] == 'decl':
                name, body = it[1], it[2]
                if name in keep or any(u.startswith(name + '.') for u in keep):
                    chunk.append(('decl', body))
                    kept += 1
                    names.append(name)
        chunk = prune(chunk)
        missing = sorted(n for n in keep if n not in names and not any(n.startswith(x + '.') for x in names))
        lines = sum(t.count('\n') + 2 for _, t in chunk)
        total_kept += lines
        if kept or missing:
            print(f'{mod}: kept {kept} decls, {lines} lines' + (f'; NOT FOUND {missing}' if missing else ''))
        if kept:
            chunks[mod] = '\n\n'.join(t for _, t in chunk)
    print(f'source lines {total_lines}, kept lines {total_kept}')
    Path(sys.argv[2]).write_text(json.dumps(chunks, ensure_ascii=False, indent=1), encoding='utf8')


if __name__ == '__main__':
    main()
