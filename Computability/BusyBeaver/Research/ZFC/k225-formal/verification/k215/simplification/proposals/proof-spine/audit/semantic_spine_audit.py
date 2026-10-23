#!/usr/bin/env python3
"""Independent, data-only semantic-spine audit. Never imports/executes ProveIt code.
Run: python3 audit/semantic_spine_audit.py [bundle-root]
Prints deterministic JSON; does not mutate source/candidate files.
This is a lexical/source audit, not a Lean elaborator or kernel check.
"""
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parents[1]
PIN = 'cbf94cb552a3b49509e0eee80e7455d4eb5974c6'
PREFIX = 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'
ENTRY = 'BusyBeaver.ZFC.KEndpoint215'
PROJECT = ('BusyBeaver.', 'FirstOrder.', 'ZF.', 'BoundedZFCConsistency.')
FAILURES = []
def check(ok, description):
    if not ok:
        FAILURES.append(description)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def gitblob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()

def strip_comments(s):
    # Retain newlines/positions; handle Lean nested block comments and strings.
    out = list(s)
    i = depth = 0
    while i < len(s):
        if depth:
            if s.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif s.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if s[i] != '\n': out[i] = ' '
                i += 1
        elif s.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif s.startswith('--', i):
            j = s.find('\n', i)
            if j < 0: j = len(s)
            out[i:j] = ' ' * (j-i); i = j
        elif s[i] == '"':
            out[i] = ' '; i += 1
            while i < len(s):
                if s[i] == '\\':
                    out[i:i+2] = '  '; i += 2
                elif s[i] == '"':
                    out[i] = ' '; i += 1; break
                else:
                    if s[i] != '\n': out[i] = ' '
                    i += 1
        else:
            i += 1
    check(depth == 0, 'Unclosed block comment in source scan')
    return ''.join(out)

def module(path):
    return path.split('/Lean/', 1)[1][:-5].replace('/', '.')

def imports(b):
    s = strip_comments(b.decode())
    return [w for row in re.findall(r'^\s*import\s+([^\n]+)', s, re.M) for w in row.split()]

baseline_root = ROOT/'review/current'
if not baseline_root.exists():
    baseline_root = ROOT/'review/snapshots/current'
baseline = {p.relative_to(baseline_root).as_posix(): p.read_bytes()
            for p in sorted(baseline_root.rglob('*.lean'))}
extra_root = ROOT/'review/snapshots/compatibility'
for p in sorted(extra_root.rglob('*.lean')):
    rel = p.relative_to(extra_root).as_posix()
    check(rel not in baseline or baseline[rel] == p.read_bytes(), 'Supplement conflicts with baseline: '+rel)
    baseline[rel] = p.read_bytes()
meta_path = ROOT/'review/all_source_metadata.json'
if not meta_path.exists():
    meta_path = ROOT/'audit/semantic_spine_baseline_metadata.json'
meta = json.loads(meta_path.read_text())
check(len(baseline) == 203, 'Expected 203 fetched baseline sources')
for path, b in baseline.items():
    check(path in meta and gitblob(b) == meta[path]['sha'], 'Git blob mismatch: ' + path)
    check(path in meta and len(b) == meta[path]['size'], 'Git byte-size mismatch: ' + path)
for p in sorted((ROOT/'lean/current').glob('*.lean')):
    check(baseline.get(PREFIX+p.name) == p.read_bytes(), 'Selected baseline diverges: ' + p.name)

# Apply unified patch exactly, without fuzzy/offset context or repository code.
lines = (ROOT/'lean/generic_spine.patch').read_text().splitlines(keepends=True)
result = dict(baseline)
i = 0
changed = []
while i < len(lines):
    check(lines[i].startswith('--- '), 'Malformed old-file patch header')
    old = lines[i][4:].rstrip('\n'); i += 1
    check(i < len(lines) and lines[i].startswith('+++ '), 'Malformed new-file patch header')
    new = lines[i][4:].rstrip('\n'); i += 1
    check(new.startswith('b/'+PREFIX), 'Unexpected patch target: ' + new)
    path = new[2:]
    check(path not in changed, 'Duplicate patch target: ' + path)
    changed.append(path)
    check(old == '/dev/null' or old == 'a/'+path, 'Unexpected old patch path: ' + old)
    orig = [] if old == '/dev/null' else baseline[path].decode().splitlines(keepends=True)
    check(old != '/dev/null' or path not in baseline, 'New module exists at baseline: ' + path)
    out = []
    cursor = 0
    while i < len(lines) and lines[i].startswith('@@ '):
        m = re.fullmatch(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@.*\n?', lines[i])
        if not m: raise ValueError('Malformed hunk header: ' + lines[i])
        old_start, old_n, new_start, new_n = [int(x) for x in (m[1], m[2] or '1', m[3], m[4] or '1')]
        i += 1
        start = old_start - 1 if old_n else old_start
        check(start >= cursor, 'Overlapping patch hunk: ' + path)
        out.extend(orig[cursor:start]); cursor = start
        used = added = 0
        check(len(out) == (new_start - 1 if new_n else new_start), 'Incorrect new hunk location: ' + path)
        while i < len(lines) and not lines[i].startswith(('@@ ', '--- ')):
            row = lines[i]; i += 1
            check(row[:1] in (' ', '+', '-'), 'Unexpected hunk line')
            if row[:1] in (' ', '-'):
                check(cursor < len(orig) and orig[cursor] == row[1:], 'Exact context mismatch: ' + path + ':' + str(cursor+1))
                cursor += 1; used += 1
            if row[:1] in (' ', '+'):
                out.append(row[1:]); added += 1
        check(used == old_n and added == new_n, 'Hunk length mismatch: ' + path)
    out.extend(orig[cursor:]); result[path] = ''.join(out).encode()
    cp = ROOT/'lean/candidate/BusyBeaver/ZFC'/Path(path).name
    check(cp.exists() and result[path] == cp.read_bytes(), 'Patch/candidate disagreement: ' + path)
check(len(changed) == 12, 'Expected 12 patch targets including WFModel compatibility import')
check(set(Path(p).name for p in changed) == set(p.name for p in (ROOT/'lean/candidate/BusyBeaver/ZFC').glob('*.lean')), 'Untracked or missing candidate file')

def graph(tree):
    return {module(p): imports(b) for p, b in tree.items()}
oldgraph, newgraph = graph(baseline), graph(result)
def closure(g, root):
    seen, missing, cycles, grey = set(), set(), [], []
    def visit(m):
        if m in grey:
            cycles.append(grey[grey.index(m):]+[m]); return
        if m in seen: return
        if m not in g:
            if m.startswith(PROJECT): missing.add(m)
            return
        seen.add(m); grey.append(m)
        for n in g[m]: visit(n)
        grey.pop()
    visit(root)
    return seen, sorted(missing), cycles

def totals(tree, mods=None):
    bs = [b for p, b in tree.items() if mods is None or module(p) in mods]
    return {'modules': len(bs), 'bytes': sum(map(len, bs)), 'lines': sum(len(b.splitlines()) for b in bs)}
oldclosure, oldmissing, oldcycles = closure(oldgraph, ENTRY)
newclosure, newmissing, newcycles = closure(newgraph, ENTRY)
check(not oldmissing and not newmissing, 'Unresolved endpoint project imports')
check(not oldcycles and not newcycles, 'Cyclic endpoint project imports')
core_closures = {}
for n in ('SingletonInfinity', 'FiniteSets', 'InductiveAttempts', 'WellFoundedPart'):
    cl, mis, cyc = closure(newgraph, 'BusyBeaver.ZFC.'+n+'Core')
    check(not mis and not cyc, 'Invalid core import closure: ' + n)
    core_closures[n] = {'modules': len(cl), 'unresolved_project_imports': mis, 'cycles': cyc}

# Exact moved region equivalence: remove only import lines and final whitespace.
boundaries = {'SingletonInfinity': 'theorem quotientBase', 'FiniteSets': 'theorem quotientBase',
              'InductiveAttempts': 'theorem quotientFiniteBase',
              'WellFoundedPart': '/-- The actual quotient supplies the fixed native GIC instance and small base. -/'}
move_checks = []
for n, marker in boundaries.items():
    src = baseline[PREFIX+n+'.lean'].decode()
    before, after = src.split(marker)
    generic = '\n'.join(x for x in before.splitlines() if not x.startswith('import ')).rstrip()
    tail = marker + after
    core = result[PREFIX+n+'Core.lean'].decode()
    core_body = '\n'.join(x for x in core.splitlines() if not x.startswith('import '))
    suffix = '\n\nend SetTheory.BusyBeaver.ZFC.'+n+'\n'
    check(core_body.endswith(suffix.rstrip('\n')), 'Unexpected core namespace ending: ' + n)
    preserved = core_body.removesuffix(suffix.rstrip('\n')).rstrip() == generic
    adapter_preserved = result[PREFIX+n+'.lean'].decode().endswith(tail)
    check(preserved and adapter_preserved, 'Moved body/tail changed: ' + n)
    adapter_names = re.findall(r'^theorem\s+(\w+)', strip_comments(tail), re.M)
    move_checks.append({'module': n, 'generic_region_sha256': sha(generic.encode()),
                        'generic_body_verbatim': preserved, 'adapter_tail_verbatim': adapter_preserved,
                        'adapter_names': adapter_names})

# Assert three clients differ only by explicitly enumerated import/name routes.
substs = {'WFModel': [('import BusyBeaver.ZFC.WFModelCore\n', 'import BusyBeaver.ZFC.WFModelCore\nimport BusyBeaver.ZFC.WellFoundedPart\n')],
          'WFRelativization': [('BusyBeaver.ZFC.WellFoundedPart', 'BusyBeaver.ZFC.WellFoundedPartCore')],
          'KQ1ZF': [('BusyBeaver.ZFC.InductiveAttempts', 'BusyBeaver.ZFC.InductiveAttemptsCore')],
          'KLowerQHyp': [('BusyBeaver.ZFC.QuotientModel', 'BusyBeaver.ZFC.KQ1Model'),
                         ('QuotientModel.memberForm', 'KQ1Model.memberForm'),
                         ('QuotientModel.sat_memberForm', 'KQ1Model.sat_memberForm')]}
for n, subs in substs.items():
    s = baseline[PREFIX+n+'.lean'].decode()
    for a, b in subs:
        check(s.count(a) == 1, 'Ambiguous route substitution: ' + n + ':' + a)
        s = s.replace(a, b)
    check(s.encode() == result[PREFIX+n+'.lean'], 'Unexpected client changes: ' + n)

# The removed CP adapters must not be referenced in the surviving endpoint graph.
removed = sorted(oldclosure - newclosure)
added = sorted(newclosure - oldclosure)
cp_prefixes = sorted(m.split('.')[-1] for m in removed if m.split('.')[-1].startswith('Quotient'))
forbidden_refs = []
for p, b in result.items():
    if module(p) not in newclosure: continue
    s = strip_comments(b.decode())
    for pre in cp_prefixes:
        for m in re.finditer(r'\b' + re.escape(pre) + r'\.[A-Za-z_][A-Za-z_0-9]*', s):
            forbidden_refs.append({'module': module(p), 'reference': m[0], 'line': s[:m.start()].count('\n')+1})
check(not forbidden_refs, 'Dangling qualified CP references in endpoint')


# Lexical public declaration inventory. This deliberately ignores generated
# structure fields and instance names; it is not a Lean name resolver.
def declarations(tree):
    found = {}
    for path, b in tree.items():
        stack = []
        names = set()
        for row in strip_comments(b.decode()).splitlines():
            m = re.match(r'^namespace\s+(\S+)', row)
            if m:
                stack.append(('namespace', m[1])); continue
            m = re.match(r'^section(?:\s+(\S+))?\s*$', row)
            if m:
                stack.append(('section', m[1])); continue
            if re.match(r'^end(?:\s+\S+)?\s*$', row):
                if stack: stack.pop()
                continue
            m = re.match(r'^(?:(?:noncomputable|private|protected|unsafe|partial)\s+)*(?:def|theorem|lemma|abbrev|structure|inductive|class|axiom)\s+([A-Za-z_][A-Za-z_0-9]*)', row)
            if m:
                ns = '.'.join(x[1] for x in stack if x[0] == 'namespace')
                names.add((ns+'.' if ns else '')+m[1])
        found[module(path)] = names
    return found
olddecls, newdecls = declarations(baseline), declarations(result)
original_declarations = set().union(*olddecls.values())
candidate_declarations = set().union(*newdecls.values())
check(original_declarations == candidate_declarations, 'Explicit public declaration name inventory changed')
# Detect short names that lost every old declaration source, or explicit
# namespace-qualified references to lost declarations. Report for manual review.
lost_reference_candidates = []
transitive_export_changes = []
baseline_unfetched_imports = []
for path, b in result.items():
    mod = module(path)
    oldmod = mod
    if mod not in oldgraph:
        if mod.rsplit('.', 1)[-1].removesuffix('Core') in boundaries and mod.endswith('Core'):
            oldmod = mod.removesuffix('Core')
        else:
            continue
    oc, old_missing, old_cycles = closure(oldgraph, oldmod)
    nc, missing, cycles = closure(newgraph, mod)
    if old_missing:
        baseline_unfetched_imports.append({'module': mod, 'imports': old_missing})
    check(not (set(missing)-set(old_missing)) and not cycles, 'New unresolved/cyclic project imports in fetched module: '+mod)
    oldnames = set().union(*(olddecls[m] for m in oc))
    newnames = set().union(*(newdecls[m] for m in nc))
    lost = oldnames-newnames
    if lost:
        transitive_export_changes.append({'module': mod, 'lost_explicit_declarations': len(lost)})
    code = strip_comments(b.decode())
    available_short = {x.rsplit('.', 1)[-1] for x in newnames}
    for full in sorted(lost):
        short = full.rsplit('.', 1)[-1]
        suffix = '.'.join(full.split('.')[-2:])
        patterns = [r'(?<![A-Za-z_0-9.])'+re.escape(suffix)+r'(?![A-Za-z_0-9])']
        if short not in available_short:
            patterns.append(r'(?<![A-Za-z_0-9.])'+re.escape(short)+r'(?![A-Za-z_0-9])')
        for match in re.finditer('|'.join(patterns), code):
            lost_reference_candidates.append({'module': mod, 'lost_declaration': full,
                'reference': match[0], 'line': code[:match.start()].count('\n')+1})
check(not lost_reference_candidates, 'Possible lost declaration references in fetched modules')

oldtot, newtot = totals(baseline, oldclosure), totals(result, newclosure)
allold, allnew = totals(baseline), totals(result)
report = {
    'audit_type': 'Independent exact-source, patch, import-graph, and lexical checks; no Lean or repository code execution',
    'pin': PIN, 'endpoint': ENTRY, 'git_blob_verified_sources': len(baseline),
    'source_pin_evidence': 'Each local source matches its recorded Git blob at the requested pin; commit/tree provenance metadata is supplied by the fetch pass, not re-fetched here.',
    'patch_sha256': sha((ROOT/'lean/generic_spine.patch').read_bytes()),
    'patch_applies_exactly_and_matches_candidates': not any('patch' in x.lower() or 'hunk' in x.lower() or 'context' in x.lower() for x in FAILURES),
    'patch_targets': changed,
    'baseline_endpoint': oldtot, 'candidate_endpoint': newtot,
    'endpoint_delta': {k: newtot[k]-oldtot[k] for k in oldtot},
    'maintained_selected_sources_before': allold, 'maintained_selected_sources_after': allnew,
    'maintained_source_delta': {k: allnew[k]-allold[k] for k in allold},
    'removed_endpoint_modules': removed, 'added_endpoint_modules': added,
    'unresolved_project_imports_before': oldmissing, 'unresolved_project_imports_after': newmissing,
    'import_cycles_before': oldcycles, 'import_cycles_after': newcycles,
    'core_closures': core_closures, 'move_checks': move_checks,
    'cp_adapter_theorem_count': sum(len(x['adapter_names']) for x in move_checks),
    'dangling_qualified_cp_references': forbidden_refs,
    'explicit_declaration_inventory_preserved': original_declarations == candidate_declarations,
    'explicit_named_declarations': len(original_declarations),
    'possible_lost_declaration_references': lost_reference_candidates,
    'transitive_export_changes': transitive_export_changes,
    'baseline_unfetched_imports_outside_endpoint': baseline_unfetched_imports,
    'external_imports': sorted({imp for m in newclosure for imp in newgraph[m] if not imp.startswith(PROJECT)}),
    'failures': FAILURES,
    'limits': ['Not a Lean parser, elaborator, kernel check, #print axioms comparison, benchmark, or proof-term-size measure.',
               'Import counts include the root and repository modules only, not implicit Init or toolchain dependencies.',
               'Maintained-source totals cover the fetched 203 source modules plus four new modules; unchanged repository files cancel in the delta.',
               'Absence of qualified dangling CP references does not establish absence of all unresolved Lean names or changes in typeclass/simp resolution.',
               'The 203 fetched sources are a selected set, not the full repository; metadata inventories 2263 files. Some non-endpoint baseline imports were not fetched. No newly unresolved project import is introduced in the fetched set.',
               'Upstream generators/build configuration were not executed.']
}
print(json.dumps(report, indent=2))
if FAILURES: sys.exit(1)
