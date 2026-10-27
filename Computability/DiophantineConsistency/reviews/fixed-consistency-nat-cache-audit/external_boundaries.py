"""Record the selected direct package boundary; do not traverse or build packages."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
PACKAGES = Path('/home/codex/src/Proofs/.lake/packages')
TOOLCHAIN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0')
ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')


def pin(path):
    path = Path(path)
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


closure = json.loads((HERE / 'closure.json').read_text())
rows = []
for module in closure['external']:
    rel = module.replace('.', '/')
    if module == 'Init':
        source = TOOLCHAIN / 'src/lean/Init.lean'
        base = TOOLCHAIN / 'lib/lean/Init'
    else:
        prefix = module.split('.')[0]
        package = {'Mathlib': 'mathlib', 'Aesop': 'aesop'}[prefix]
        source = PACKAGES / package / (rel + '.lean')
        base = PACKAGES / package / '.lake/build/lib/lean' / rel
    objects = []
    missing = []
    for suffix in ['.olean', '.olean.server', '.olean.private', '.ir']:
        p = Path(str(base) + suffix)
        if p.is_file():
            objects.append(pin(p))
        else:
            missing.append(str(p))
    if not Path(str(base) + '.olean').is_file():
        raise RuntimeError('Missing direct external object: ' + module)
    rows.append({'module': module, 'source': pin(source), 'objects': objects,
                 'missing_optional_companions': missing})
result = {
    'status': 'EXISTING_DIRECT_PACKAGE_BOUNDARIES_PINNED_NO_PACKAGE_BUILD',
    'scope': '51 direct external names including Init. Exact current source/artifact hashes; package transitive closures are existing accepted4.32 build boundaries, not independently replayed here. No broad Mathlib.Tactic import appears in selected custom closure.',
    'driver': pin(__file__), 'compiler': pin(TOOLCHAIN / 'bin/lean'),
    'root_toolchain': pin(ROOT / 'lean-toolchain'),
    'root_manifest': pin(ROOT / 'lake-manifest.json'),
    'central_manifest': pin(Path('/home/codex/src/Proofs/lake-manifest.json')),
    'modules': rows,
}
(HERE / 'external-boundaries.json').write_text(json.dumps(result, indent=2) + '\n')
print('Pinned', len(rows), 'direct external boundaries; no builds')
