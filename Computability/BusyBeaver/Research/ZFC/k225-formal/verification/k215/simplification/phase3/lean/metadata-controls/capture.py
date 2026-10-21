"""Collect immutable phase-three evidence bytes; never runs a compiler."""
from pathlib import Path
import json
from evidence import binary_name, digest

HERE = Path(__file__).resolve().parent
FORMAL = 'Computability/BusyBeaver/Research/ZFC/k225-formal'


def arguments(parser):
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--basis', type=Path, default=Path('/tmp/k215-proof-phase2/lean-run1'))
    parser.add_argument('--build', type=Path, default=Path('/tmp/k215-proof-phase3/build.py'))
    parser.add_argument('--basis-build', type=Path, default=Path('/tmp/k215-proof-phase2/build.py'))
    parser.add_argument('--basis-review', type=Path, default=Path('/tmp/k215-proof-phase2/live-review.json'))
    parser.add_argument('--basis-reviewer', type=Path, default=Path('/tmp/k215-proof-phase2/review.py'))
    parser.add_argument('--stdout', type=Path, help='Optional original driver console log')


def collect(args):
    run, basis = args.run.resolve(), args.basis.resolve()
    members = {}

    def add(name, path):
        path = Path(path)
        assert path.is_file() and not path.is_symlink(), path
        assert name not in members and not binary_name(path)
        members[name] = path.read_bytes()

    for name in ('owner.json', 'inventory.json', 'completed.json', 'basis-completed.json',
                 'basis-inventory.json', 'basis-logs.json', 'toolchain.json',
                 'reviewed-driver.py', 'result.json'):
        add('execution/' + name, run / name)
    owner = json.loads(members['execution/owner.json'])
    repo = Path(owner['repo'])
    for name in ('owner.json', 'inventory.json', 'completed.json', 'phase1-completed.json',
                 'basis-objects.json', 'toolchain.json', 'reviewed-driver.py', 'result.json'):
        add('basis/' + name, basis / name)
    add('basis/phase1-result.json', repo / FORMAL / 'verification/k215/simplification/lean/result.json')
    add('basis/build.py', args.basis_build)
    add('basis/live-review.json', args.basis_review)
    add('basis/review.py', args.basis_reviewer)
    add('review/build.py', args.build)
    for name in ('evidence.py', 'capture.py', 'review.py', 'review_saved.py', 'publish.py'):
        add('review/' + name, HERE / name)
    if args.stdout is not None:
        add('review/driver.stdout', args.stdout)
    inventory = json.loads(members['execution/inventory.json'])
    done = json.loads(members['execution/completed.json'])
    old = json.loads(members['basis/completed.json'])
    basis_logs = json.loads(members['execution/basis-logs.json'])
    for entry in inventory['modules']:
        module = entry['module']
        add('execution/sources/' + module.replace('.', '/') + '.lean', entry['source'])
        add('execution/logs/' + module + '.log', done[module]['log'])
        add('basis/logs/' + module + '.log', basis_logs[module])
        assert digest(members['basis/logs/' + module + '.log']) == old[module]['log_sha256']
    for folder in [run / 'attempts', *sorted(run.glob('audit-*'))]:
        if not folder.exists():
            continue
        assert folder.is_dir() and not folder.is_symlink()
        for path in sorted(folder.rglob('*')):
            assert not path.is_symlink(), path
            if path.is_file() and not binary_name(path):
                add('execution/' + path.relative_to(run).as_posix(), path)
    return members
