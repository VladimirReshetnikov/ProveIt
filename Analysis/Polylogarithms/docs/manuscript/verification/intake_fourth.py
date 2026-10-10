"""Preserve the fourth incoming batch without modifying delivered bytes."""
from pathlib import Path, PurePosixPath
import hashlib, json, subprocess, zipfile

B = Path(__file__).resolve().parents[1]
R = B.parents[3]
V = B / 'verification'
revision = 'a0a90ef31877f98be437191c48b46f02d5456867'
packages = {
    'ProveIt_Integral_Distributions_Reflection_Jets.zip': 'integral-distribution-reflection-jets',
    'polylog_integral_distribution_research.zip': 'integral-distribution-reflection',
    'ProveIt_Polylogarithm_Continuation.zip': 'fractional-cayley-scaling',
    'ProveIt_RealOrder_Threshold.zip': 'real-order-threshold',
    'polylogarithms_uniform_continuation_20261010.zip': 'finite-golden-uniform-continuation',
}
records = []
for archive, folder in packages.items():
    name = 'docs/incoming/' + archive
    blob = subprocess.check_output(['git', 'show', revision + ':' + name], cwd=R)
    assert blob == (R / name).read_bytes(), name
    files = []
    with zipfile.ZipFile(R / name) as z:
        members = [n for n in z.namelist() if not n.endswith('/')]
        roots = {PurePosixPath(n).parts[0] for n in members}
        assert len(roots) == 1, roots
        for n in members:
            parts = PurePosixPath(n).parts
            assert len(parts) >= 2 and not any(p in ('..', '.') or ':' in p or '\\' in p for p in parts), n
            rel = Path('reports') / folder / Path(*parts[1:])
            target = B.parent / rel
            assert target.resolve().is_relative_to((B.parent / 'reports' / folder).resolve())
            data = z.read(n)
            if target.exists():
                assert target.read_bytes() == data, target
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(data)
            files.append(dict(path=rel.as_posix(), sha256=hashlib.sha256(data).hexdigest(), bytes=len(data)))
    records.append(dict(archive=name, archive_git_revision=revision,
                        archive_sha256=hashlib.sha256(blob).hexdigest(),
                        destination='reports/' + folder, files=files))
(V / 'fourth-incoming-archives.json').write_text(json.dumps(records, indent=2) + '\n', encoding='utf-8')
attributes = R / '.gitattributes'
text = attributes.read_text(encoding='utf-8')
for folder in packages.values():
    rule = 'Analysis/Polylogarithms/docs/reports/' + folder + '/** -text -whitespace'
    if rule not in text:
        text += '\n' + rule + '\n'
attributes.write_text(text, encoding='utf-8')
print('Preserved', sum(len(a['files']) for a in records), 'members from', len(records), 'archives.')
