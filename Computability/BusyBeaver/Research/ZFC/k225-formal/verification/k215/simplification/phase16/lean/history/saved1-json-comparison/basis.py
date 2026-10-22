"""Validate the pinned local phase15 packet, without executing archived code."""
from pathlib import Path
import hashlib, importlib.util, json, sys, tarfile
HERE = Path(__file__).resolve().parent
digest = lambda b: hashlib.sha256(b).hexdigest()

def load(repo):
    raw = (HERE / 'basis-reference.json').read_bytes()
    assert digest(raw) == '6e74b1f683a748957d07c652e3a7ed2f691c665bebdf8d6e0c2316c8d6cf8f45'
    ref = json.loads(raw)
    directory = Path(repo) / ref['repository_relative_directory']
    def pinned():
        data = {n: (directory / n).read_bytes() for n in ref['files']}
        for n, b in data.items():
            assert not (directory / n).is_symlink()
            assert {'sha256': digest(b), 'bytes': len(b)} == ref['files'][n]
        return data
    files = pinned()
    names = [('basis', 'basis.py'), ('packet', 'packet.py'), ('phase15_reader', 'review_saved.py')]
    previous = {n: sys.modules.get(n) for n, _ in names}
    bytecode = sys.dont_write_bytecode
    try:
        sys.dont_write_bytecode = True
        for n, filename in names:
            spec = importlib.util.spec_from_file_location(n, directory / filename)
            mod = importlib.util.module_from_spec(spec); sys.modules[n] = mod; spec.loader.exec_module(mod)
        ancestor = []
        old_load = sys.modules['basis'].load
        def cached(path):
            assert Path(path).resolve() == Path(repo).resolve()
            if not ancestor: ancestor.append(old_load(path))
            return ancestor[0]
        sys.modules['basis'].load = cached
        checked = sys.modules['phase15_reader'].review(directory, basis_repo=repo, repo=None)
        assert checked['status'] == 'PASS_SAVED_PHASE15' and not checked['current_sources_checked']
        helper = sys.modules['packet']; members = {}
        with tarfile.open(directory / 'execution.tar.gz', 'r:gz') as archive:
            for item in archive:
                helper.safe(item.name); assert item.isfile() and item.name not in members
                members[item.name] = archive.extractfile(item).read()
        assert helper.manifest(members) == json.loads(files['index.json'])
        prior = ancestor[0][0]
        data = {'member:' + n: b for n, b in members.items()}
        for path, route in json.loads(members['path-map.json']).items():
            b = (members if route['storage'] == 'packet' else prior)[route['key']]
            assert digest(b) == route['sha256'] and len(b) == route['bytes']
            data['path:' + path] = b
        assert pinned() == files
        return data, helper
    finally:
        sys.dont_write_bytecode = bytecode
        for n, old in previous.items():
            if old is None: sys.modules.pop(n, None)
            else: sys.modules[n] = old
