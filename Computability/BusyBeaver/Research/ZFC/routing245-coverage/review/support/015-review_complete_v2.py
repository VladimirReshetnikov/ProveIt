#!/usr/bin/env python3
"""Independent existing-evidence review, never a proof/guard/generator runner.

Invoke only after root announces the terminal complete batch and supplies its
exact digest. All supplied artifacts are parsed as data. The script has no
subprocess, import-loader, eval, exec, compiler, or network facility.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json
import re

ROOT = Path('/home/codex/.codex/worktrees/ec20/Proofs')
BASE = Path('/tmp/zfc-routing245-lean/coverage-production')
HERE = Path(__file__).resolve().parent
MANIFEST = BASE / 'v4/sources/generation.json'
MANIFEST_SHA = 'b79fe539f343ca2f8979ada70f534f2ee08fb2361598a87f39c1e410fe6c32bc'
GUARD = BASE / 'v4/check-production-v4.py'
GUARD_SHA = 'c37473de1eacb7a47a397e49bbff9b0bed9eeb1efbebea21f3c0835ecf42f7b5'
FINAL = 'BusyBeaver.ZFC.SitesRouting245'
NS = 'SetTheory.BusyBeaver.ZFC.SitesRouting245.'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
TOOLS = {'Init', 'Lean.Elab.Tactic.Omega'}
COMPILER_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
COMPILER_VERSION = 'Lean (version 4.32.0, x86_64-unknown-linux-gnu, commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)'
PILOTS = {
    'd343f1c8b0618bf19b46bd5140da920f757e1e9550b1bf2cd75f84811edcceb1',
    'f69992ea47733e19e84e8c1d25c16200ebd261329e8de4bea2634359074408eb',
    '30ddc599a0511ca665e6258cdd245787dcc3ae1d2b348b6b8ab83b778b35e5d2',
}
FAILED = [
    ('all-run1/unit013/verification.json', '59e6ab1764a0062e4d272d0c6bf8af0ed7aba370eb3dab020eaeaa446bfe6a12', -9, True),
    ('v2/cut42-run1/unit000/verification.json', 'e4c402e883fe27e58e7caba2542a51adfee9cf97a33fdcc293b4fff8e723bab5', 1, False),
    ('v3/remaining-run1/unit008/verification.json', 'c000fe17683398cfedc53f5d692fa556087d5974f0316d1b96d13ee40ac173cc', 1, False),
]
SUPPORT = [
    BASE / 'independent-generated-family-review.json',
    BASE / 'independent-production-guard-preparation-review.json',
    BASE / 'independent-unit013-timeout-source-review.json',
    BASE / 'v2/independent-successor-source-review.json',
    BASE / 'v2/independent-generated-family-review.json',
    BASE / 'v3/independent-refinement-review.json',
    BASE / 'v3/independent-refinement-actual-review.json',
    BASE / 'v4/independent-source-family-review.json',
    BASE / 'v4/independent-refinement-actual-review.json',
    BASE / 'publication-design/independent-dynamic-builder-review.json',
    BASE.parent / 'coverage-subtree-pilots/independent-subtree-pattern-review.json',
    BASE.parent / 'coverage-subtree-pilots/independent-subtree-source-guard-review.json',
    HERE / 'plan.md', HERE / 'complete-review.schema.json', HERE / 'closeout-inventory.json',
]


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2) + '\n').encode()


def compact(text):
    return ' '.join(text.split())


def strip_comments(text):
    """Nested Lean block comments, then line comments; no source evaluation."""
    out, index, depth = [], 0, 0
    while index < len(text):
        pair = text[index:index + 2]
        if pair == '/-':
            depth += 1
            out.append(' ')
            index += 2
        elif pair == '-/' and depth:
            depth -= 1
            index += 2
        else:
            if not depth:
                out.append(text[index])
            elif text[index] == '\n':
                out.append('\n')
            index += 1
    if depth:
        raise ValueError('Unclosed Lean comment')
    return re.sub(r'--[^\n]*', '', ''.join(out))


def imports(text):
    return re.findall(r'^import\s+(\S+)\s*$', strip_comments(text), re.M)


def bools(path):
    return '[' + ', '.join('true' if x == '1' else 'false' for x in path) + ']'


def proposition(path):
    return f'allSites SiteRouting245.checkSite {bools(path[::-1])} (descend TreeRouting245.tree {bools(path)}) = true'


def bits(text):
    if not text.strip():
        return ''
    values = [v.strip() for v in text.split(',')]
    if any(v not in {'true', 'false'} for v in values):
        raise ValueError('Nonliteral Bool list')
    return ''.join('1' if v == 'true' else '0' for v in values)


class Review:
    def __init__(self, args):
        self.args = args
        self.checks = 0
        self.refs = 0
        self.aliases = {}
        self.pins = {}
        self.json_cache = {}
        self.text_cache = {}
        self.import_cache = {}
        self.selected = {}
        self.records = {}
        self.batches = {}
        self.closures = {}
        self.module_identity = {}
        self.resolutions = {}
        self.summaries = []
        self.axioms = collections.Counter()

    def require(self, value, message):
        self.checks += 1
        if not value:
            raise ValueError(message)

    def pin(self, path, expected):
        self.refs += 1
        p = Path(path).absolute()
        self.require(re.fullmatch('[0-9a-f]{64}', expected) is not None, 'Malformed hash ' + str(p))
        resolved = str(p.resolve(strict=True))
        alias = str(p)
        self.require(alias not in self.aliases or self.aliases[alias] == (resolved, expected), 'Conflicting alias ' + alias)
        self.require(resolved not in self.pins or self.pins[resolved] == expected, 'Conflicting current bytes ' + resolved)
        if resolved not in self.pins:
            self.require(sha(resolved) == expected, 'Changed current input ' + alias)
            self.pins[resolved] = expected
        self.aliases[alias] = (resolved, expected)
        return p

    def descriptor(self, path):
        p = Path(path).resolve()
        digest = sha(p)
        self.pin(p, digest)
        return dict(path=str(p), sha256=digest)

    def read(self, ref):
        p = self.pin(ref['path'], ref['sha256'])
        key = str(p.resolve())
        if key not in self.json_cache:
            self.json_cache[key] = json.loads(p.read_text())
        return self.json_cache[key]

    def text(self, path):
        key = str(Path(path).resolve())
        if key not in self.text_cache:
            self.text_cache[key] = Path(key).read_text()
        return self.text_cache[key]

    def source_imports(self, path):
        key = str(Path(path).resolve())
        if key not in self.import_cache:
            self.import_cache[key] = imports(self.text(key))
        return self.import_cache[key]

    def setup(self):
        self.plan = self.read(dict(path=str(MANIFEST), sha256=MANIFEST_SHA))
        self.pin(GUARD, GUARD_SHA)
        m = self.plan
        self.require((len(m['units']), len(m['reused_units'])) == (599, 25), 'Frozen family count')
        self.require((m['complete_probes'], m['complete_callers'], m['generated_probes'], m['generated_callers']) == (958, 961, 905, 905), 'Frozen audit count')
        self.require((m['leaves'], m['guard_cases'], m['decoder_depth']) == (6460, 8391, 51), 'Frozen tree count')
        self.units = {}
        for index, u in enumerate(m['units']):
            self.require(u['module'] not in self.units, 'Repeated generated module')
            self.units[u['module']] = dict(u, origin='new', index=index,
                source_path=MANIFEST.parent / u['source'], audit_path=MANIFEST.parent / u['audit'])
        for u in m['reused_units']:
            name = u['full_module']
            self.require(name not in self.units, 'Repeated reused module')
            self.units[name] = dict(u, module=name, source_path=Path(u['source']['path']),
                audit_path=Path(u['audit']['path']), source_sha256=u['source']['sha256'], audit_sha256=u['audit']['sha256'])
        self.require({u['record']['sha256'] for u in m['reused_units'] if u['origin'] == 'pilot'} == PILOTS, 'Pilot whitelist')
        for u in self.units.values():
            for role in ('source', 'audit'):
                self.pin(u[role + '_path'], u[role + '_sha256'])
        for ref in m['inputs'] + [m['generator']]:
            self.pin(ref['path'], ref['sha256'])
        self.require((sum(u['probes'] for u in self.units.values()), sum(u['callers'] for u in self.units.values())) == (958, 961), 'Independent audit sum')

    def collect(self, ref, top=False):
        b = self.read(ref)
        key = str(Path(ref['path']).resolve())
        if key in self.batches:
            self.require(self.batches[key]['sha256'] == ref['sha256'], 'Conflicting batch')
            return
        self.require(b['manifest']['sha256'] == MANIFEST_SHA and b['guard']['sha256'] == GUARD_SHA, 'Batch family/guard')
        self.require(not b['prepare_only'] and b['status'] in {'PASS_SELECTED_UNITS', 'PASS_COMPLETE_COVERAGE'}, 'Nonterminal/failed selected batch')
        self.require(b.get('active_unit') is None and b.get('failed_unit') is None, 'Active or failed selected batch')
        self.require(b['serial'] and b['shared_wall_seconds_per_unit'] == 120, 'Batch execution policy')
        self.require(not any(b[k] for k in ('compiler_version_query_performed', 'dependency_build', 'downloads')), 'Batch capability')
        if top:
            self.require(b['status'] == 'PASS_COMPLETE_COVERAGE', 'Root terminal complete PASS is mandatory')
            self.require((b['complete_generated_units'], b['complete_probes'], b['complete_callers']) == (599, 958, 961), 'Complete batch census')
            self.require(b['selected_unit_indices'] == list(range(292, 599)), 'Final selection differs')
            self.top = b
        self.batches[key] = dict(path=key, sha256=ref['sha256'], indices=b['selected_unit_indices'])
        for prior in b['prior_batches']:
            self.collect(prior)
        self.require([x['unit_index'] for x in b['completed_units']] == b['selected_unit_indices'], 'Incomplete selected range')
        for row in b['completed_units']:
            index = row['unit_index']
            self.require(0 <= index < 599 and self.plan['units'][index]['module'] == row['module'] and row['status'] == 'PASS', 'Invalid batch row')
            canonical = dict(path=str(Path(row['record']['path']).resolve()), sha256=row['record']['sha256'])
            if row['module'] in self.selected:
                self.require(self.selected[row['module']] == canonical, 'Conflicting selected record')
            self.selected[row['module']] = canonical

    def literal_tree(self):
        path = ROOT / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProgramRouting245.lean'
        self.pin(path, self.plan['program_source_sha256'])
        src = strip_comments(self.text(path))
        rows = {}
        for match in re.finditer(r'^private def row(\d+) : Row := \(\(\.(\w+)(?: (\d+))?\), \(\.(\w+)(?: (\d+))?\)\)$', src, re.M):
            i, left, a, right, b = match.groups()
            rows[int(i)] = ((left, int(a) if a else None), (right, int(b) if b else None))
        halt_rows = re.findall(r'^private def row(\d+) : Row := \(\(\.node (\d+)\), \.halt\)$', src, re.M)
        self.require(halt_rows == [('186', '175')] and 186 not in rows, 'Exact unparenthesized halt row')
        rows[186] = (('node', 175), ('halt', None))
        self.require(set(rows) == set(range(203)), 'Independent 203-row parse')
        self.require(re.search(r'^  root := 202$', src, re.M) and re.search(r'^def tree : Tree := t202$', src, re.M), 'Actual decoder root')
        self.tree = {}
        cursor = 0
        def descend(edge, prefix):
            nonlocal cursor
            start = cursor
            op, arg = edge
            if op == 'node':
                self.require(arg in rows, 'Missing DAG row')
                for child in rows[arg]:
                    self.require(child[0] != 'node' or child[1] < arg, 'Cyclic DAG row')
                left = descend(rows[arg][0], prefix + '0')
                right = descend(rows[arg][1], prefix + '1')
                summary = dict(lo=start, hi=cursor, nodes=left['nodes'] + right['nodes'] + 1,
                    leaves=left['leaves'] + right['leaves'], guards=left['guards'] + right['guards'], height=1 + max(left['height'], right['height']))
            else:
                self.require(op in {'inc', 'decnz', 'brk', 'cont', 'halt'}, 'Unknown leaf')
                cursor += 1
                summary = dict(lo=start, hi=cursor, nodes=0, leaves=1, guards=2 if op == 'decnz' else 1, height=0)
            self.tree[prefix] = summary
            return summary
        root = descend(('node', 202), '')
        self.require((root['nodes'], root['leaves'], root['guards'], root['height']) == (6459, 6460, 8391, 51), 'Actual expanded tree census')
        for cut in self.plan['cut_frontier']:
            self.require(all(cut[k] == self.tree[cut['path']][k] for k in ('lo', 'hi', 'nodes', 'leaves', 'guards', 'height')), 'Cut does not match literal subtree')
        self.require([c['lo'] for c in self.plan['cut_frontier']] == [0] + [c['hi'] for c in self.plan['cut_frontier'][:-1]] and self.plan['cut_frontier'][-1]['hi'] == 6460, 'Outer frontier partition')

    def source_graph(self):
        self.literal_tree()
        declarations = {}
        by_module = {}
        for module, u in self.units.items():
            src = strip_comments(self.text(u['source_path']))
            audit = strip_comments(self.text(u['audit_path']))
            self.require(not re.search(r'\b(?:sorry|axiom|native_decide)\b|set_option\s+(?:maxRecDepth|maxHeartbeats)', src), 'Forbidden source proof shortcut')
            if u['origin'] == 'new':
                self.require(self.source_imports(u['source_path']) == u['imports'], 'Manifest import list')
            self.require(imports(audit) == [module], 'Typed audit imports another module')
            probes = re.findall(r'^#print axioms (\S+)\s*$', audit, re.M)
            self.require(len(probes) == u['probes'] and len(re.findall(r'^example\b', audit, re.M)) == u['callers'], 'Actual audit syntax census')
            if module == FINAL:
                continue
            namespaces = re.findall(r'^namespace (\S+)\s*$', src, re.M)
            self.require(len(namespaces) == 1, 'Coverage namespace')
            matches = list(re.finditer(r'^theorem (\w+)\s*:\s*(.*?)\s*:=\s*(.*?)(?=^theorem |^end |\Z)', src, re.M | re.S))
            self.require(len(matches) == u['probes'] == len(re.findall(r'^theorem ', src, re.M)), 'Unparsed theorem')
            by_module[module] = []
            for match in matches:
                name, typ, body = match.groups()
                full = namespaces[0] + '.' + name
                self.require(full not in declarations, 'Duplicate theorem')
                p = re.fullmatch(r'allSites SiteRouting245\.checkSite \[([^]]*)\] \(descend TreeRouting245\.tree \[([^]]*)\]\) = true', compact(typ))
                self.require(p is not None, 'Nonliteral coverage proposition ' + full)
                reverse, path = map(bits, p.groups())
                self.require(reverse == path[::-1] and path in self.tree, 'Wrong consumed prefix ' + full)
                body = compact(body)
                children = []
                if body == 'by decide +kernel':
                    if u['origin'] == 'new':
                        self.require(self.tree[path]['guards'] <= 32, 'Oversized new closed block')
                else:
                    prefix = f'allSites_join SiteRouting245.checkSite {bools(reverse)} (descend TreeRouting245.tree {bools(path + "0")}) (descend TreeRouting245.tree {bools(path + "1")}) '
                    self.require(body.startswith(prefix), 'Join does not use both literal children ' + full)
                    children = body[len(prefix):].split()
                    self.require(len(children) == 2 and all(c.startswith('SetTheory.BusyBeaver.ZFC.') for c in children), 'Join child names')
                declarations[full] = dict(module=module, name=name, path=path, children=children, proposition=compact(typ))
                by_module[module].append(full)
            self.require(probes == by_module[module], 'Audit theorem order differs')
            examples = re.findall(r'^example\s*:\s*(.*?)\s*:=\s*([\w.]+)\s*(?=^example|\Z)', audit, re.M | re.S)
            expected_direct = 1 if u['origin'] == 'pilot' else len(matches)
            self.require(len(examples) == expected_direct, 'Non-direct typed caller')
            for typ, theorem in examples:
                full = theorem if '.' in theorem else namespaces[0] + '.' + theorem
                self.require(full in by_module[module] and compact(typ) == declarations[full]['proposition'], 'Typed caller proposition differs')
            if u['origin'] == 'pilot':
                d = declarations[by_module[module][0]]
                p, rev = bools(d['path']), bools(d['path'][::-1])
                tail = f'example (Q : List Bool) (e : Edge) (hl : LeafAt (descend TreeRouting245.tree {p}) Q e) : SiteRouting245.checkSite ({rev}.reverse ++ Q) e = true := allSites_sound SiteRouting245.checkSite hl {rev} checked'
                self.require(compact(audit).endswith(compact(tail)), 'Pilot arbitrary leaf caller')
        self.require(len(declarations) == 955, 'Nonfinal theorem count')
        for name, d in declarations.items():
            for bit, child in zip('01', d['children']):
                self.require(child in declarations and declarations[child]['path'] == d['path'] + bit, 'Incorrect join dependency ' + name)
        visited, active = set(), set()
        def follow(name):
            self.require(name not in active, 'Cyclic theorem join')
            if name in visited:
                return
            active.add(name)
            for child in declarations[name]['children']:
                follow(child)
            active.remove(name)
            visited.add(name)
        follow(NS + 'join_234')
        self.require(visited == set(declarations) and declarations[NS + 'join_234']['path'] == '', 'Final root omits a theorem')
        closed = [d for d in declarations.values() if not d['children']]
        self.require((len(closed), len(declarations) - len(closed)) == (478, 477), 'Independent refined graph census')
        intervals = sorted((self.tree[d['path']]['lo'], self.tree[d['path']]['hi']) for d in closed)
        self.require(intervals[0][0] == 0 and intervals[-1][1] == 6460 and all(a[1] == b[0] for a, b in zip(intervals, intervals[1:])), 'Closed blocks do not partition all leaves')
        self.require(sum(self.tree[d['path']]['guards'] for d in closed) == 8391, 'Guard coverage count')
        for c in self.plan['cut_frontier']:
            self.require(c['theorem'] in declarations and declarations[c['theorem']]['path'] == c['path'], 'Outer cut theorem mismatch')
        for j in self.plan['join_plan']:
            d = declarations[j['theorem']]
            refs = [self.plan['cut_frontier'][i]['theorem'] if kind == 'cut' else self.plan['join_plan'][i]['theorem'] for kind, i in [j['left'], j['right']]]
            self.require(d['path'] == j['path'] and d['children'] == refs, 'Outer both-child join mismatch')
        for refinement in self.plan['refinements']:
            for p in refinement['parts']:
                self.require(declarations[NS + p['name']]['path'] == p['path'], 'Refined part path')
                self.require(all(p[k] == self.tree[p['path']][k] for k in ('lo', 'hi', 'nodes', 'leaves', 'guards', 'height')), 'Refined part literal statistics')
            for j in refinement['joins']:
                self.require(declarations[NS + j['name']]['path'] == j['path'] and declarations[NS + j['name']]['children'] == [NS + j['left'], NS + j['right']], 'Refined both-child join')
        final = strip_comments(self.text(self.units[FINAL]['source_path']))
        expected = '''theorem all_sites : allSites SiteRouting245.checkSite [] TreeRouting245.tree = true :=
          SetTheory.BusyBeaver.ZFC.SitesRouting245.join_234
        theorem actual_walk_checked (P : List Bool) (e : Edge) (d : Nat)
          (hw : walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d)) :
          SiteRouting245.checkSite (consume P d) e = true :=
          allSites_walk SiteRouting245.checkSite ProgramRouting245.program TreeRouting245.tree
            TreeRouting245.tree_eq all_sites P e d hw
        theorem actual_walk_exists (P : List Bool) :
          ∃ e d, walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d) :=
          allSites_walk_total SiteRouting245.checkSite ProgramRouting245.program TreeRouting245.tree
            TreeRouting245.tree_eq all_sites P'''
        actual = final[final.index('theorem all_sites'):final.rindex('end SetTheory.')]
        self.require(compact(actual) == compact(expected), 'Final theorem scope/complete body differs')
        audit = strip_comments(self.text(self.units[FINAL]['audit_path']))
        expected_clients = '''example : allSites SiteRouting245.checkSite [] TreeRouting245.tree = true := all_sites
        example (P : List Bool) (e : Edge) (d : Nat)
          (hw : walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d)) :
          SiteRouting245.checkSite (consume P d) e = true := actual_walk_checked P e d hw
        example (P : List Bool) :
          ∃ e d, walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d) :=
          actual_walk_exists P'''
        self.require(compact(audit[audit.index('example :'):]) == compact(expected_clients), 'Final typed arbitrary-pointer clients differ')
        self.graph = dict(closed_blocks=478, binary_joins=477, covered_leaves=6460, covered_guards=8391,
            arbitrary_pointer_endpoint=True, theorem_graph=declarations)

    def register_pair(self, module, source_sha, object_sha):
        pair = (source_sha, object_sha)
        self.require(module not in self.module_identity or self.module_identity[module] == pair, 'Conflicting selected module source/object ' + module)
        self.module_identity[module] = pair

    def closure(self, source, providers, tools):
        seen, active, used_tools = set(), set(), {'Init'}
        def visit(path):
            for mod in self.source_imports(path):
                if mod in tools:
                    used_tools.add(mod)
                    continue
                self.require(mod in providers and mod not in active, 'Missing/cyclic source provider ' + mod)
                if mod in seen:
                    continue
                active.add(mod)
                visit(providers[mod]['source'])
                active.remove(mod)
                seen.add(mod)
        visit(source)
        self.require(seen == set(providers) and used_tools == set(tools), 'Exact independent source DFS differs')
        return seen

    def first(self, r, module):
        roots = [Path(x) for x in r['LEAN_PATH'].split(':')]
        roots.append(Path(r['compiler']['path']).parent.parent / 'lib/lean')
        relative = Path(*module.split('.')).with_suffix('.olean')
        candidates = [base / relative for base in roots if (base / relative).is_file()]
        self.require(bool(candidates), 'Missing current first provider ' + module)
        return candidates[0]

    def check_first(self, r, module, expected_path, expected_sha, reported):
        first = self.first(r, module)
        target = str(Path(expected_path).resolve())
        self.require(str(first.resolve()) == target, 'Current first provider changed ' + module)
        reported_path = reported.get('actual_first', reported.get('path'))
        self.require(reported.get('module', module) == module, 'Saved provider name differs')
        self.require(reported['sha256'] == expected_sha and str(Path(reported_path).resolve()) == target, 'Saved first provider differs ' + module)
        self.resolutions[str(first)] = target
        self.pin(first, expected_sha)

    def validate(self, module, ref):
        u = self.units[module]
        r = self.read(ref)
        self.require(r['status'] == 'PASS' and r['prepare_only'] is False and r['before'] == r['after'], 'Not a complete actual PASS ' + module)
        self.require((r['named_axiom_probes'], r['callers']) == (u['probes'], u['callers']), 'Actual audit census ' + module)
        self.require(r['warnings'] == {'source': 0, 'audit': 0}, 'Selected warning')
        for key in ('all_input_provider_postchecks', 'all_fresh_objects_unchanged_after_audit', 'source_object_recorded_before_audit', 'only_standard_axioms', 'exact_project_import_closure'):
            self.require(r[key] is True, 'Missing actual evidence flag ' + key)
        self.require(r['limits'] == dict(threads=1, memory_mebibytes=4096, shared_wall_seconds=120, proof_limits='Lean defaults'), 'Actual proof limits')
        self.require((r['site_fuel'], r['margin']) == (4000, 64), 'Actual checker parameters')
        self.require(not any(r[k] for k in ('dependency_build', 'downloads', 'compiler_version_query_performed')), 'Unexpected execution capability')
        self.require(not r['compiler']['compiler_version_query_performed'], 'Compiler version query')
        self.require((r['compiler']['sha256'], r['compiler']['version']) == (COMPILER_SHA, COMPILER_VERSION), 'Pinned compiler boundary differs')
        self.pin(r['compiler']['path'], r['compiler']['sha256'])
        for path, digest in r['before'].items():
            self.pin(path, digest)
        if u['origin'] == 'new':
            self.require(r['manifest']['sha256'] == MANIFEST_SHA and r['before'][str(GUARD)] == GUARD_SHA and r['unit_index'] == u['index'], 'New unit changed input family')
        for role in ('source', 'audit'):
            q = r[role]
            self.require(q['sha256'] == u[role + '_sha256'], 'Wrong actual ' + role)
            self.pin(q['path'], q['sha256'])
            self.pin(q['snapshot'], q['sha256'])
        self.require([c['label'] for c in r['commands']] == ['source', 'audit'], 'Actual command order')
        snaproot = Path(r['audit']['snapshot']).parent
        fresh_candidate, = r['fresh_modules']
        for command in r['commands']:
            self.require(command['exit_code'] == 0 and not command.get('timed_out', False) and not command.get('interrupted', False), 'Failed actual command')
            self.require(command['command'][0] == r['compiler']['path'] and command['command'][1:3] == ['-j1', '-M4096'], 'Actual compiler invocation')
            self.require('warning:' not in command['output'] and 'sorryAx' not in command['output'] and "declaration uses 'sorry'" not in command['output'], 'Raw warning or sorry')
            self.pin(command['log'], hashlib.sha256(command['output'].encode()).hexdigest())
            self.require(command['command'][-1] == r[command['label']]['snapshot'], 'Command compiled wrong source')
            expected_command = [r['compiler']['path'], '-j1', '-M4096', '--root=' + str(snaproot)]
            if command['label'] == 'source':
                expected_command += ['-o', fresh_candidate['path']]
            expected_command += [r[command['label']]['snapshot']]
            self.require(command['command'] == expected_command and Path(command['cwd']).resolve() == snaproot.resolve(), 'Unexpected compiler arguments or working directory')
        self.require(sum(c['seconds'] for c in r['commands']) < 120, 'Shared deadline exceeded')
        audit = self.text(u['audit_path'])
        names = re.findall(r'^#print axioms (\S+)\s*$', audit, re.M)
        namespace = 'SetTheory.BusyBeaver.ZFC.' + module.rsplit('.', 1)[1] + '.' if u['origin'] == 'pilot' else NS
        self.require(names == [namespace + n for n in u['probe_names']], 'Manifest named probes differ')
        matches = re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", r['commands'][1]['output'], re.S)
        reports = [dict(name=n, axioms=[v.strip() for v in block.split(',') if v.strip()]) for n, block in matches]
        self.require(reports == r['actual_axiom_sets'] and [q['name'] for q in reports] == names and len(reports) == u['probes'], 'Raw ordered axiom reports')
        self.require(all(set(q['axioms']) <= ALLOWED for q in reports), 'Nonstandard axiom')
        self.require(len(re.findall(r'^example\b', audit, re.M)) == u['callers'], 'Typed caller count')
        for q in reports:
            self.axioms[','.join(sorted(q['axioms']))] += 1
        self.require(len(r['fresh_modules']) == 1, 'Fresh module count')
        fresh = r['fresh_modules'][0]
        self.require(fresh['module'] == module and fresh['source_sha256'] == u['source_sha256'], 'Fresh source binding')
        self.require(all(r['source_pass_object'][k] == fresh[k] for k in ('module', 'path', 'sha256', 'source_sha256')) and r['source_pass_object']['source_command_index'] == 0, 'Pre-audit object capture')
        self.pin(fresh['path'], fresh['sha256'])
        self.require(not Path(fresh['path']).is_symlink(), 'Fresh object is a reused symlink')
        self.check_first(r, module, fresh['path'], fresh['sha256'], r['fresh_first_provider_before_audit'])
        self.register_pair(module, fresh['source_sha256'], fresh['sha256'])
        providers = {q['module']: q for q in r['reused_modules']}
        actuals = {q['module']: q for q in r['actual_first_providers']}
        tools = {q['module']: q for q in r['toolchain_providers']}
        self.require(len(providers) == len(r['reused_modules']) == r['project_module_count'] and set(actuals) == set(providers) and len(actuals) == len(r['actual_first_providers']), 'Project provider census')
        self.require(set(tools) == TOOLS and len(r['toolchain_providers']) == 2, 'Tool boundary')
        self.require(r['external_project_boundaries'] == [], 'Unexpected external project boundary')
        closure = self.closure(r['source']['path'], providers, tools)
        self.closures[module] = closure
        for name, q in providers.items():
            for role in ('source', 'object'):
                self.pin(q[role], q[role + '_sha256'])
                key = str(Path(q[role]).resolve())
                self.require(r['before'].get(key, r['before'].get(q[role])) == q[role + '_sha256'], 'Provider absent from before record')
            self.register_pair(name, q['source_sha256'], q['object_sha256'])
            self.check_first(r, name, q['object'], q['object_sha256'], actuals[name])
        for name, q in tools.items():
            self.pin(q['object'], q['object_sha256'])
            self.check_first(r, name, q['object'], q['object_sha256'], dict(actual_first=q['actual_first'], sha256=q['object_sha256']))
        for evidence in r['provider_evidence']:
            parent = self.read(evidence)
            self.require(parent['status'] == 'PASS' and parent['before'] == parent['after'], 'Selected parent is not an actual PASS')
        if u['origin'] == 'pilot':
            self.require(ref['sha256'] in PILOTS and 'preparation' not in r, 'Pilot preparation exception')
        else:
            prep = self.read(r['preparation'])
            self.require(prep['status'] == 'PREPARED_NOT_BUILT' and prep['prepare_only'] is True and prep['commands'] == [] and prep['fresh_modules'] == [], 'Invalid separate preparation')
            self.require(prep['before'] == prep['after'] == r['before'] and prep['all_input_provider_postchecks'], 'Preparation input binding')
            for field in ('source', 'audit', 'manifest', 'reused_modules', 'actual_first_providers', 'toolchain_providers', 'compiler'):
                self.require(prep[field] == r[field], 'Preparation changed ' + field)
            for path, digest in prep['before'].items():
                self.pin(path, digest)
        self.records[module] = r
        self.summaries.append(dict(module=module, record=ref, inputs=len(r['before']), projects=len(providers),
            probes=u['probes'], callers=u['callers'], seconds={c['label']: c['seconds'] for c in r['commands']}, fresh=fresh))

    def failed_history(self):
        result = []
        for relative, digest, exit_code, timeout in FAILED:
            ref = dict(path=str(BASE / relative), sha256=digest)
            r = self.read(ref)
            self.require(r['status'] == 'FAIL' and [c['label'] for c in r['commands']] == ['source'], 'Historical failure altered')
            self.require(not r['fresh_modules'] and r['commands'][0]['exit_code'] == exit_code and r['commands'][0]['timed_out'] == timeout, 'Historical failure scope')
            for role in ('source', 'audit'):
                self.pin(r[role]['snapshot'], r[role]['sha256'])
            for role in ('manifest', 'generator'):
                self.pin(r[role]['path'], r[role]['sha256'])
            old_guards = [(p, h) for p, h in r['before'].items() if Path(p).name.startswith('check-production') and Path(p).suffix == '.py']
            active_name = 'check-production.py' if relative.startswith('all-') else 'check-production-' + relative.split('/')[0] + '.py'
            self.require(sum(Path(p).name == active_name for p, h in old_guards) == 1, 'Historical active guard identity ambiguous')
            for path, digest in old_guards:
                self.pin(path, digest)
            for c in r['commands']:
                self.pin(c['log'], hashlib.sha256(c['output'].encode()).hexdigest())
            result.append(dict(record=ref, status=r['status'], source=r['source'], audit=r['audit'], commands=[dict(label=c['label'], exit_code=c['exit_code'], timed_out=c['timed_out'], log=c['log']) for c in r['commands']]))
        return result

    def finish(self):
        self.require(set(self.selected) == set(self.units), 'Missing selected module')
        self.require(self.top['final_record'] == self.selected[FINAL], 'Aggregate final record differs')
        for i, module in enumerate(self.units):
            self.validate(module, self.selected[module])
            if i % 64 == 63:
                print(json.dumps(dict(reviewed=i + 1, total=624)), flush=True)
        final = self.records[FINAL]
        self.require(final['project_module_count'] == 646, 'Final actual project closure')
        self.require(set(self.units) - {FINAL} <= self.closures[FINAL], 'Final source misses selected module')
        base = self.closures[FINAL] - (set(self.units) - {FINAL})
        self.require(len(base) == 23, 'Final generic base count')
        for module in self.units:
            if module != FINAL:
                q = next(x for x in final['reused_modules'] if x['module'] == module)
                r = self.records[module]
                self.require((q['source_sha256'], q['object_sha256']) == (r['source']['sha256'], r['fresh_modules'][0]['sha256']), 'Final actual selected ancestor differs')
        self.require((sum(x['probes'] for x in self.summaries), sum(x['callers'] for x in self.summaries)) == (958, 961), 'Actual final census')
        failures = self.failed_history()
        supporting = [self.descriptor(p) for p in SUPPORT + [Path(__file__).resolve()]]
        # Hash all distinct current bytes again; also reject a cache-symlink retarget.
        for path, digest in self.pins.items():
            self.require(sha(path) == digest, 'Current input changed during review ' + path)
        for alias, (target, digest) in self.aliases.items():
            self.require(str(Path(alias).resolve(strict=True)) == target, 'Input alias retargeted during review ' + alias)
        for alias, target in self.resolutions.items():
            self.require(str(Path(alias).resolve(strict=True)) == target, 'First provider retargeted during review')
        output = self.args.output.resolve()
        self.require(not output.exists() and not output.is_relative_to(ROOT) and not output.is_relative_to(BASE), 'Use absent external review output')
        output.mkdir(parents=True)
        detail = dict(status='CLEAN_COMPLETE_ROUTING245_COVERAGE_DETAIL', findings=[], checks=self.checks,
            record_reference_checks=self.refs, unique_current_paths=len(self.pins), current_path_aliases=len(self.aliases),
            selected_units=self.summaries, actual_axiom_set_census=dict(self.axioms),
            graph=self.graph, final_generic_base=sorted(base), selected_import_graph={m: sorted(c) for m, c in self.closures.items()},
            current_input_hashes=self.pins, current_path_bindings={k: dict(resolved=v[0], sha256=v[1]) for k, v in self.aliases.items()},
            historical_failures=failures, actual_batches=list(self.batches.values()),
            no_compiler_guard_generator_builder_version_execution=True)
        detail_path = output / 'review-detail.json'
        detail_path.write_bytes(encoded(detail))
        supporting.append(dict(path=str(detail_path), sha256=sha(detail_path)))
        script_copy = output / 'reviewer-source.py'
        script_copy.write_bytes(Path(__file__).read_bytes())
        supporting.append(dict(path=str(script_copy), sha256=sha(script_copy)))
        selected = [dict(module=m, **self.selected[m]) for m in self.units]
        receipt = dict(status='CLEAN_COMPLETE_ROUTING245_COVERAGE_EXISTING_EVIDENCE_REVIEW', findings=[],
            manifest=dict(path=str(MANIFEST), sha256=MANIFEST_SHA), guard=dict(path=str(GUARD), sha256=GUARD_SHA),
            complete_batch=dict(path=str(self.args.complete_batch.resolve()), sha256=self.args.complete_batch_sha),
            probes=958, callers=961, selected_modules=624, final_projects=646, selected_records=selected,
            final_record=dict(module=FINAL, **self.selected[FINAL]),
            all_selected_current_inputs_checked=True, all_selected_actual_providers_checked=True,
            all_fresh_objects_recorded_before_audit=True, supporting_artifacts=supporting,
            reviewer_role='Independent of the coverage source emitters, proof guards and root execution. Reviewer authored the separate publication builder and earlier source/partial-evidence reviews; this independently authored script rederives the source theorem graph, actual records and provider bindings without invoking any supplied program.',
            scope='Complete external Lean coverage of the exact routed245 decoder: all6460 leaves/8391 guards, 478 closed blocks and477 both-child joins, arbitrary program pointer clients. 599new+25reused modules, no external coverage premise. This is not a binary bootstrap/runtime endpoint or an internal PA equivalence.',
            checks=self.checks, unique_current_paths=len(self.pins), no_proof_replay=True)
        receipt_path = output / 'complete-review.json'
        receipt_path.write_bytes(encoded(receipt))
        print(json.dumps(dict(receipt=str(receipt_path), sha256=sha(receipt_path), checks=self.checks,
            selected_modules=624, probes=958, callers=961, final_projects=646), indent=2), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--complete-batch', type=Path, default=BASE / 'v4/final307-run1/batch.json')
    parser.add_argument('--complete-batch-sha', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    review = Review(args)
    # Fail closed on the exact terminal root-reported bytes before any review output.
    top = review.read(dict(path=str(args.complete_batch.resolve()), sha256=args.complete_batch_sha))
    review.require(top['status'] == 'PASS_COMPLETE_COVERAGE', 'Wait for root terminal PASS notification')
    review.setup()
    review.collect(dict(path=str(args.complete_batch.resolve()), sha256=args.complete_batch_sha), top=True)
    review.require(len(review.batches) == 11, 'Expected ten prior batches plus terminal batch')
    for u in review.plan['reused_units']:
        review.require(u['full_module'] not in review.selected, 'Reused/new module collision')
        review.selected[u['full_module']] = dict(path=str(Path(u['record']['path']).resolve()), sha256=u['record']['sha256'])
    review.source_graph()
    review.finish()


if __name__ == '__main__':
    main()
