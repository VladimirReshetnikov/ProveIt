"""Read-only adaptive-expression dependency plan. No Lean, overlay or mutation of inputs."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import shutil
import subprocess
import tomllib

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = R / 'Computability/DiophantineConsistency'
OUT = D / 'research/adaptive-expression2011-cache-plan.json'
PINS = {}
OBSERVATIONS = 0


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def record(path):
    p = Path(path)
    p = p if p.is_absolute() else R / p
    raw = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw))


def check(expected):
    global OBSERVATIONS
    got = record(expected['path'])
    need(got['sha256'] == expected['sha256'], 'hash mismatch: ' + got['path'])
    need('bytes' not in expected or got['bytes'] == expected['bytes'], 'byte count')
    PINS[got['path']] = got
    OBSERVATIONS += 1
    return got


def pin(path):
    return check(record(path))


def load(path):
    p = pin(path)
    return p, json.loads(Path(p['path']).read_text())


def imports(path):
    text = Path(path).read_text()
    out = []
    i = depth = 0
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            i += 2
        elif pair == '--':
            while i < len(text) and text[i] != '\n':
                i += 1
        else:
            out.append(text[i])
            i += 1
    need(depth == 0, 'balanced comments')
    text = ''.join(out)
    result = [] if re.search(r'^\s*prelude\s*$', text, re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', text, re.M):
        result.extend(line.split())
    return list(dict.fromkeys(result))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    if args.verify:
        plan = json.loads(OUT.read_text())
        for p in plan['pins']:
            check(p)
        for m in plan['modules']:
            need(imports(m['source']['path']) == m['imports'], 'current header: ' + m['module'])
        print(json.dumps(dict(status='FROZEN_PINS_AND_HEADERS_PASS', plan=record(OUT),
                              observations=OBSERVATIONS), indent=2))
        return
    need(not OUT.exists(), 'preserve existing frozen plan')
    need(shutil.disk_usage('/tmp').free >= 512 * 1024**2, 'disk reserve')
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip()
    gi, graph = load(D / 'reviews/native-adaptive-graph-root-replay/INPUTS.json')
    gr, graph_root = load(D / 'reviews/native-adaptive-graph-root-replay/ROOT.json')
    gm, graph_mf = load(D / 'reviews/native-adaptive-graph-root-replay/FILES.json')
    for row in graph_mf:
        check(dict(row, path=str(Path(gm['path']).parent / row['path'])))
    ni, narrow = load(D / 'reviews/current-equation-narrow-dependency-replay.json')
    nr, narrow_root = load(D / 'reviews/current-equation-narrow-root-replay/ROOT.json')
    bm, boundary_parent = load(D / 'reviews/current-positive-zero2011-refresh/manifest.json')
    need(graph_root['status'] == 'PASS' and narrow_root['state']['status'] == 'PASS',
         'accepted historical terminal records')
    old = {}
    for m in graph['selected_custom']:
        old[m['module']] = dict(source=m['source'], object=m['object'], origin=gi)
    for m in narrow['modules']:
        if m['module'] not in old and isinstance(m.get('object'), str):
            old[m['module']] = dict(
                source=dict(path=m['source'], sha256=m['source_sha256']),
                object=dict(path=m['object'], sha256=m['object_sha256']), origin=ni)
    for m in graph_root['records']:
        old[m['module']] = dict(source=m['source'], object=m['object'], origin=gr)
    for m in narrow_root['state']['completed']:
        old[m['module']] = dict(
            source=dict(path=m['source'], sha256=m['source_sha256']),
            object=dict(path=m['object'], sha256=m['object_sha256']), origin=nr)

    lake = pin(R / 'lakefile.toml')
    roots = {x['name']: R / x.get('srcDir', '.')
             for x in tomllib.loads(Path(lake['path']).read_text())['lean_lib']}
    modules = {}
    order = []
    active = set()
    boundaries = set()

    def visit(n):
        if n in modules:
            return
        if n.split('.')[0] not in roots:
            boundaries.add(n)
            return
        need(n not in active, 'acyclic: ' + n)
        active.add(n)
        p = roots[n.split('.')[0]] / Path(*n.split('.')).with_suffix('.lean')
        src = pin(p)
        deps = imports(p)
        for dep in deps:
            visit(dep)
        active.remove(n)
        modules[n] = dict(module=n, source=src, imports=deps)
        order.append(n)

    direct = ['DiophantineConsistency.NativeAdaptiveGraph',
              'DiophantineConsistency.CurrentKernelData2011',
              'DiophantineConsistency.NaturalExpressionSemiring']
    for n in direct:
        visit(n)
    changed, fresh, reused = [], [], []
    for n in order:
        m = modules[n]
        need(n in old, 'historical provider record: ' + n)
        o = old[n]
        m['historical_provider'] = o
        if m['source']['sha256'] != o['source']['sha256']:
            changed.append(n)
        causes = [d for d in m['imports'] if d in fresh]
        if n in changed or causes:
            fresh.append(n)
            m.update(mode='FRESH_CURRENT_SOURCE_REQUIRED', changed=n in changed,
                     affected_dependencies=causes, selected_objects=[])
            p = Path(o['object']['path'])
            actual = pin(p) if p.is_file() else None
            m['excluded_object_observation'] = actual
            m['excluded_object_matches_historical_record'] = (
                actual is not None and actual['sha256'] == o['object']['sha256'])
        else:
            reused.append(n)
            m.update(mode='REUSE_SOURCE_AND_DEPENDENCY_IDENTICAL',
                     selected_objects=[check(o['object'])])
    need(len(order) == 52 and len(changed) == 6 and len(fresh) == 24 and len(reused) == 28,
         'expected bounded refresh partition')
    need(not any(n.startswith('Foundation.') for n in order), 'no Foundation imports')
    need(len(boundaries) == 35, 'boundary count')

    inherited = {m['module']: dict(source=m['source'], artifacts=m['artifacts'], origin=gi)
                 for m in graph['external_boundary']}
    for m in boundary_parent['external_boundary']:
        inherited.setdefault(m['module'], dict(source=m['source'],
            artifacts=[m['object']] + m['companions'], origin=bm))
    tc = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0')
    packages = [p for p in graph['LEAN_PATH'][1:] if '/.lake/packages/' in p]
    package_roots = [Path(p) for p in packages]
    need(package_roots, 'explicit package search')
    search = package_roots + [tc / 'lib/lean']
    external = []
    new_boundary = []
    for n in sorted(boundaries):
        rel = Path(*n.split('.'))
        obj = next((r / rel.with_suffix('.olean') for r in search
                    if (r / rel.with_suffix('.olean')).is_file()), None)
        need(obj is not None, 'boundary provider: ' + n)
        if n == 'Init':
            src = tc / 'src/lean/Init.lean'
        else:
            need(n.startswith('Mathlib.'), 'expected package boundary')
            src = R / '.lake/packages/mathlib' / rel.with_suffix('.lean')
        row = dict(module=n, source=pin(src), artifacts=[])
        for suffix in ['.olean', '.olean.private', '.olean.server', '.ir']:
            p = obj.with_name(obj.name[:-len('.olean')] + suffix)
            if p.is_file():
                row['artifacts'].append(pin(p))
        trace = obj.with_suffix('.trace')
        if trace.is_file():
            row['trace'] = pin(trace)
        hist = inherited.get(n)
        if hist:
            need(row['source']['sha256'] == hist['source']['sha256'], 'boundary source: ' + n)
            for p in hist['artifacts']:
                check(p)
                matches = [a for a in row['artifacts'] if Path(a['path']).name == Path(p['path']).name]
                need(len(matches) == 1 and matches[0]['sha256'] == p['sha256'], 'boundary artifact: ' + n)
            row['origin'] = hist['origin']
        else:
            new_boundary.append(n)
            row['origin'] = 'CURRENT_V4_32_PACKAGE_BOUNDARY_NOT_IN_TWO_SELECTED_HISTORICAL_INVENTORIES'
        external.append(row)
    need(new_boundary == ['Mathlib.Data.Fintype.Sum', 'Mathlib.Data.Nat.Digits.Defs'],
         'explicit new package boundaries')
    compiler = check(graph['compiler'])
    identities = [pin(R / 'lean-toolchain'), pin(R / 'lake-manifest.json'),
                  pin(R / '.lake/packages/mathlib/lean-toolchain'),
                  pin(R / '.lake/packages/mathlib/lake-manifest.json')]
    proposal = pin(D / 'research/adaptive-expression2011-proposal.md')
    auditor = pin(__file__)
    for p in list(PINS.values()):
        check(p)
    counts = dict(custom=52, Foundation=0, changed_sources=6, fresh_prerequisites=24,
                  cached_custom=28, cached_custom_artifacts=28, boundary_primaries=35,
                  boundary_artifacts=sum(len(m['artifacts']) for m in external),
                  new_package_boundary_names=len(new_boundary), new_main_check_leaves=4)
    plan = dict(status='READ_ONLY_PLAN_NO_OVERLAY_NO_COMPILER_REQUIRES_ROOT_REVIEW',
        head=head, final_head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=R, text=True).strip(),
        proposal=proposal, auditor=auditor, direct_imports=direct, counts=counts,
        historical_evidence=[gi, gr, gm, ni, nr, bm], modules=[modules[n] for n in order],
        topological_order=order, changed_sources=changed, fresh_prerequisites=fresh,
        reused_modules=reused, external=external, new_boundary_names=new_boundary,
        compiler=compiler, package_identity=identities, boundary_search=[str(p) for p in search],
        prospective_outputs='24 fresh prerequisites, then narrow main/Checks and wide main/Checks; no accepted output overwritten',
        pins=list(PINS.values()), observations=OBSERVATIONS, unique_paths=len(PINS))
    OUT.write_text(json.dumps(plan, indent=2) + '\n')
    print(json.dumps(dict(plan=record(OUT), counts=counts,
                          observations=OBSERVATIONS, unique_paths=len(PINS)), indent=2))


if __name__ == '__main__':
    main()
