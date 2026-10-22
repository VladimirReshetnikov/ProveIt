"""Capture or review phase16 evidence. No compiler, generator or archive code runs."""
from pathlib import Path
import argparse, io, json, tarfile
import basis, packet
HERE = Path(__file__).resolve().parent
HELPERS = ['basis.py','basis-reference.json','packet.py','review.py','controls.py','README.md','config.json','freeze.json']

def saved(directory, repo, current=None, loaded=None):
    directory = Path(directory); prior, h = loaded or basis.load(repo)
    result = json.loads((directory / 'result.json').read_bytes()); index = json.loads((directory / 'index.json').read_bytes())
    assert result['status'] == 'PASS_CAPTURED_PHASE16'
    assert packet.sha(directory / 'execution.tar.gz') == result['archive_sha256'] and packet.sha(directory / 'index.json') == result['index_sha256']
    members = {}
    with tarfile.open(directory / 'execution.tar.gz', 'r:gz') as archive:
        for item in archive:
            h.safe(item.name); assert item.isfile() and item.name not in members
            b = archive.extractfile(item).read(); assert index[item.name] == {'sha256': packet.digest(b), 'bytes': len(b)}; members[item.name] = b
    assert h.manifest(members) == index and len(members) == result['members']
    for n in HELPERS: assert (directory / n).read_bytes() == members['review/' + n]
    freeze = json.loads(members['review/freeze.json'])
    for n, pin in freeze['files'].items(): assert packet.digest(members['review/' + n]) == pin
    checked, _, _, _ = packet.validate(members, prior, h, current)
    assert {k:v for k,v in checked.items() if k != 'current_sources_checked'} == result['checked']
    assert result['live_postcheck'] == json.loads(members['live-postcheck.json'])
    assert result['live_postcheck'] == {'status':'PASS_LIVE_OBJECT_SOURCE_LOG_INPUT_TOOLCHAIN_POSTCHECK','current_providers':[195,78],'basis_providers':[194,71],'current_source_copies':212,'endpoint_objects':2}
    return {**checked, 'status':'PASS_SAVED_PHASE16', 'archive_sha256':result['archive_sha256'], 'members':len(members)}

def capture(output, repo):
    output = Path(output); assert not output.exists()
    prior, h = basis.load(repo); cfg = json.loads((HERE / 'config.json').read_bytes())
    freeze = json.loads((HERE / 'freeze.json').read_bytes())
    for n, pin in freeze['files'].items(): assert packet.sha(HERE / n) == pin
    adoption = json.loads(Path(packet.INTEGRATION + '/adoption.json').read_bytes())
    history = {packet.ROOT + '/' + r['path']: packet.ROOT + '/' + r['before_snapshot'] for r in adoption['files']}
    reference = json.loads((HERE / 'basis-reference.json').read_bytes())
    parent_pins = {packet.ROOT + '/' + reference['repository_relative_directory'] + '/' + n: r['sha256'] for n, r in reference['files'].items()}
    members, routes = {}, {}
    def add(path, pin=None):
        path = str(path); h.safe(Path(path).name); actual = history.get(path, path)
        b = Path(actual).read_bytes(); digest = packet.digest(b)
        if pin is not None: assert digest == pin, path
        key = 'path:' + path
        if key in prior and prior[key] == b: route = {'storage':'phase15','key':key,'sha256':digest,'bytes':len(b)}
        else:
            key = 'blobs/' + digest; members[key] = b
            route = {'storage':'packet','key':key,'sha256':digest,'bytes':len(b)}
        if path in routes: assert routes[path] == route, path
        routes[path] = route
        return b
    for p, pin in cfg['context'].items(): add(p, pin)
    for root in packet.RUNS:
        inv = json.loads(add(root + '/inventory.json')); done = json.loads(add(root + '/completed.json'))
        result = json.loads(add(root + '/result.json')); before = json.loads(add(root + '/before.json')); toolchain = json.loads(add(root + '/toolchain.json'))
        binaries = {v['path'] for v in toolchain.values() if isinstance(v, dict) and 'path' in v}
        for p, pin in before['inputs'].items():
            if p in parent_pins:
                assert pin == parent_pins[p] and packet.sha(p) == pin
            elif p not in binaries and '.olean' not in Path(p).suffixes: add(p, pin)
        for row in inv['modules']:
            m = row['module']; b = add(row['source'], row['source_sha256'])
            key = 'sources/' + m.replace('.', '/') + '.lean'
            if key in members: assert members[key] == b
            members[key] = b; rec = done[m]; add(rec['log'], rec['log_sha256'])
            if rec['origin'] == 'candidate_fresh': add(Path(rec['log']).with_name('record.json')); add(rec['source'], row['source_sha256'])
        for a in result['audits']:
            add(a['source'], a['source_sha256']); add(a['log'], a['log_sha256'])
            add(root + '/audit-' + a['module'] + '/' + a['module'] + '.json')
    for n in HELPERS: members['review/' + n] = (HERE / n).read_bytes()
    members['config.json'] = (HERE / 'config.json').read_bytes(); members['path-map.json'] = packet.dump(routes)
    checked, accepted, object_pins, binary_pins = packet.validate(members, prior, h, repo)
    # Postcheck after all endpoint audits; historical paths retain before bytes.
    for p, pin in {**object_pins, **binary_pins}.items(): assert packet.sha(p) == pin, p
    for p, route in routes.items(): assert packet.sha(history.get(p, p)) == route['sha256'], p
    for root, rows, done, result in accepted:
        cache = Path(root) / 'objects'
        assert {str(p.relative_to(cache)) for p in cache.rglob('*.olean')} == {m.replace('.', '/') + '.olean' for m in rows}
        for m, rec in done.items():
            obj = cache / (m.replace('.', '/') + '.olean')
            assert obj.is_file() and (not obj.is_symlink() if rec['origin'] == 'candidate_fresh' else obj.is_symlink())
            if rec['origin'] != 'candidate_fresh':
                prior_root = packet.RUNS[0] if rec['origin'] == 'secondary_checked' else packet.OLD[0 if rec['origin'] == 'phase15_primary_checked' else 1]
                assert obj.resolve() == (Path(prior_root) / 'objects' / (m.replace('.', '/') + '.olean')).resolve()
            for parent in obj.parents:
                assert not parent.is_symlink()
                if parent == cache: break
            assert packet.sha(obj) == rec['object_sha256'] and packet.sha(rec['log']) == rec['log_sha256']
        for rec in result['audits']:
            adir = Path(root) / ('audit-' + rec['module'])
            assert packet.sha(adir / (rec['module'] + '.olean')) == rec['object_sha256']
            assert packet.sha(adir / (rec['module'] + '.lean')) == rec['source_sha256']
    post = {'status':'PASS_LIVE_OBJECT_SOURCE_LOG_INPUT_TOOLCHAIN_POSTCHECK','current_providers':[195,78],'basis_providers':[194,71],'current_source_copies':212,'endpoint_objects':2}
    members['live-postcheck.json'] = packet.dump(post)
    for name in members: h.safe(name)
    output.mkdir(parents=True)
    for n in HELPERS: (output / n).write_bytes((HERE / n).read_bytes())
    with tarfile.open(output / 'execution.tar.gz', 'w:gz') as archive:
        for name, b in sorted(members.items()):
            item = tarfile.TarInfo(name); item.size = len(b); item.mtime = 0; item.mode = 0o644; archive.addfile(item, io.BytesIO(b))
    (output / 'index.json').write_bytes(packet.dump(h.manifest(members)))
    result = {'status':'PASS_CAPTURED_PHASE16','archive_sha256':packet.sha(output / 'execution.tar.gz'),'index_sha256':packet.sha(output / 'index.json'),'members':len(members),'checked':{k:v for k,v in checked.items() if k != 'current_sources_checked'},'live_postcheck':post}
    (output / 'result.json').write_bytes(packet.dump(result)); return result

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('mode', choices=['capture','saved']); p.add_argument('--packet', type=Path, required=True); p.add_argument('--basis-repo', type=Path, required=True); p.add_argument('--repo', type=Path); p.add_argument('--output', type=Path, required=True); a = p.parse_args()
    assert not a.output.exists()
    result = capture(a.packet, a.basis_repo) if a.mode == 'capture' else saved(a.packet, a.basis_repo, a.repo)
    a.output.write_bytes(packet.dump(result)); print(json.dumps(result, indent=2))
