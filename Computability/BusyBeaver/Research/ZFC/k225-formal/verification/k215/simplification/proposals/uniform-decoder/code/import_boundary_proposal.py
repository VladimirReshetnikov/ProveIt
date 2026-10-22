#!/usr/bin/env python3
"""Generate a review-only patch; never modify the supplied ProveIt checkout.

The patch separates two semantic lemmas/modules from historical program
endpoints. The prediction concerns static imports, not kernel acceptance or
elapsed build time. Invoke with PROVEIT_ROOT OUTPUT_DIR.
"""

from __future__ import annotations

import difflib
import hashlib
import json
from pathlib import Path
import sys
import subprocess

BASELINE = '2ca3a5c16f0876d2cab842056353c03a1ed2f5f0'
LEAN_DIR = Path('Computability/BusyBeaver/Lean')
MOD_DIR = LEAN_DIR / 'BusyBeaver/ZFC'
GEN = Path('Computability/BusyBeaver/Research/ZFC/k225-formal/generate_l2k222.py')


def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


def propose(repo: Path):
    before: dict[Path, str] = {}
    after: dict[Path, str] = {}

    def read(name):
        path = MOD_DIR / (name + '.lean')
        before[path] = (repo / path).read_text()
        return path, before[path]

    p, t = read('ZFNative')
    start = t.index('/-- The semantic content of a model of `ZFax_s`. -/')
    end = t.index('/-- **Every model of ZF is a model of the native theory.** -/')
    model_decl = t[start:end]
    after[MOD_DIR / 'ZFModels.lean'] = (
        'import BusyBeaver.ZFC.InternalOrd\n\n'
        '/-! Semantic content of a ZF model, independent of historical program endpoints.\n'
        'Moved verbatim from ZFNative.lean; its declaration name is preserved. -/\n\n'
        'namespace SetTheory.BusyBeaver.ZFC.ZFNative\n'
        'open InternalOrd\n'
        'universe u\nvariable {V : Type u}\n\n' + model_decl +
        'end SetTheory.BusyBeaver.ZFC.ZFNative\n'
    )
    after[p] = ('import BusyBeaver.ZFC.ZFModels\n' + t[:start] +
                '-- models_ZF is provided by ZFModels with its original name.\n\n' + t[end:])

    p, t = read('WFModel')
    ns = t.index('namespace SetTheory.BusyBeaver.ZFC.WFModel')
    cut = t.index('/-- The needed closure is supplied by the existing literal GIC witness case. -/')
    prefix = t[ns:cut]
    suffix = t[cut:]
    after[MOD_DIR / 'WFModelCore.lean'] = (
        'import BusyBeaver.ZFC.WFRelativization\n'
        'import BusyBeaver.ZFC.PSCCalibration\n\n'
        '/-! The general well-founded-part model construction.\n'
        'Declarations are copied verbatim from WFModel; the CPGIC specialization\n'
        'and historical enumerator consequences remain in its compatibility wrapper. -/\n\n'
        + prefix + 'end SetTheory.BusyBeaver.ZFC.WFModel\n'
    )
    after[p] = (
        'import BusyBeaver.ZFC.WFModelCore\n'
        'import BusyBeaver.ZFC.QuotientZF0\n'
        'import BusyBeaver.ZFC.QuotientCPGIC\n\n'
        '/-! Compatibility wrapper and CPGIC specialization; public names are preserved. -/\n\n'
        'namespace SetTheory.BusyBeaver.ZFC.WFModel\n'
        'open Form WellFoundedPart WFRelativization\n'
        'universe u\nvariable {V : Type u} {mem : V → V → Prop}\n\n' + suffix
    )

    for name, old, new in [
        ('ConstructibleChoice', 'ZFNative', 'ZFModels'),
        ('KQ1ZF', 'WFTheory', 'WFModelCore'),
        ('L2Lib222', 'Enum254', 'Code254'),
    ]:
        p, t = read(name)
        anchor = f'import BusyBeaver.ZFC.{old}\n'
        assert t.count(anchor) == 1
        after[p] = t.replace(anchor, f'import BusyBeaver.ZFC.{new}\n')
        if name == 'KQ1ZF':
            # KQ1ZF uses ordinary_infinity_of_container directly; it was
            # previously supplied transitively by WFTheory/QuotientZF0.
            after[p] = 'import BusyBeaver.ZFC.InductiveAttempts\n' + after[p]

    # Keep the maintained generator in sync with the reduced L2Lib222 import.
    before[GEN] = (repo / GEN).read_text()
    anchor = 'SUBS = [\n'
    assert before[GEN].count(anchor) == 1
    after[GEN] = before[GEN].replace(anchor, anchor +
        '    ("import BusyBeaver.ZFC.Enum254", "import BusyBeaver.ZFC.Code254"),\n')

    # Source extraction is an identity check, not a substitute for elaboration.
    assert model_decl in after[MOD_DIR / 'ZFModels.lean']
    assert prefix in after[MOD_DIR / 'WFModelCore.lean']
    return before, after, {
        'models_ZF_verbatim_sha256': sha(model_decl),
        'WFModel_generic_declarations_verbatim_sha256': sha(prefix),
    }


def closure(repo: Path, overrides: dict[Path, str]):
    pending = ['BusyBeaver.ZFC.KEndpoint215']
    seen = set()
    missing = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        p = LEAN_DIR / Path(module.replace('.', '/')).with_suffix('.lean')
        source = overrides.get(p)
        if source is None:
            if not (repo / p).is_file():
                missing.add(module)
                continue
            source = (repo / p).read_text()
        seen.add(module)
        for line in source.splitlines():
            if line.startswith('import '):
                pending.extend(line[7:].split())
    return seen, missing


def main():
    repo = Path(sys.argv[1]).resolve()
    out = Path(sys.argv[2]).resolve()
    observed = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip()
    if observed != BASELINE:
        raise SystemExit(f'Expected baseline {BASELINE}; found {observed}. Re-audit before adapting.')
    out.mkdir(parents=True, exist_ok=True)
    before, after, bodies = propose(repo)
    patch = []
    for path in sorted(after, key=str):
        old = before.get(path, '')
        patch.extend(difflib.unified_diff(old.splitlines(keepends=True),
                     after[path].splitlines(keepends=True),
                     fromfile=('a/' + str(path)) if path in before else '/dev/null',
                     tofile='b/' + str(path)))
    (out / 'import_boundaries.patch').write_text(''.join(patch))
    for path, text in after.items():
        dest = out / 'proposed' / path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(text)
    a, missing_a = closure(repo, {})
    b, missing_b = closure(repo, after)
    def volume(modules, overrides):
        values = []
        for module in modules:
            p = LEAN_DIR / Path(module.replace('.', '/')).with_suffix('.lean')
            values.append(overrides[p] if p in overrides else (repo / p).read_text())
        return {'lines': sum(len(t.splitlines()) for t in values),
                'bytes': sum(len(t.encode()) for t in values)}
    before_volume, after_volume = volume(a, {}), volume(b, after)
    removed = []
    for module in sorted(a - b):
        p = LEAN_DIR / Path(module.replace('.', '/')).with_suffix('.lean')
        text = (repo / p).read_text()
        removed.append({'module': module, 'lines': len(text.splitlines()),
                        'bytes': len(text.encode()), 'sha256': sha(text)})
    report = {
        'baseline': BASELINE,
        'status': 'SOURCE_GRAPH_PROJECTION_NOT_KERNEL_CHECKED',
        'scope': 'Modules physically under Computability/BusyBeaver/Lean only; external project libraries are boundary nodes.',
        'before_local_modules': len(a), 'after_local_modules': len(b),
        'source_volume_before': before_volume, 'source_volume_after': after_volume,
        'source_volume_removed_net': {k: before_volume[k] - after_volume[k] for k in before_volume},
        'removed': removed, 'added': sorted(b - a),
        'removed_source_lines': sum(x['lines'] for x in removed),
        'removed_source_bytes': sum(x['bytes'] for x in removed),
        'boundary_before': sorted(missing_a), 'boundary_after': sorted(missing_b),
        'inputs': [{'path': str(p), 'sha256': sha(t)} for p,t in before.items()],
        'verbatim_extractions': bodies,
        'acceptance_required': ['Compile affected modules in dependency order.',
             'Regenerate L2 modules and inspect any unexpected delta.',
             'Run the two original K215 endpoint clients and axiom reports.',
             'Run legacy endpoint clients that import ZFNative/WFModel.',
             'Refresh source-bound receipts only after the checks pass.'],
    }
    (out / 'import_boundaries.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ['status', 'before_local_modules',
        'after_local_modules', 'removed_source_lines', 'removed_source_bytes', 'added']}, indent=2))
    for x in removed:
        print(x['module'], x['lines'])


if __name__ == '__main__':
    main()
