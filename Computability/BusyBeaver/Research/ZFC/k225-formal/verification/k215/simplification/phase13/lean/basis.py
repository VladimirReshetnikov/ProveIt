"""Resolve the exact local phase12 evidence; never execute archive members."""
from pathlib import Path
import hashlib, importlib.util, json, sys, tarfile
HERE = Path(__file__).resolve().parent
PIN = '66112698049384540650932c48b6780b8fe5be46a6d5f20ba375d48b8f569b67'
digest = lambda b: hashlib.sha256(b).hexdigest()

def load(repo):
    raw = (HERE / 'basis-reference.json').read_bytes()
    assert digest(raw) == PIN
    ref = json.loads(raw)
    directory = Path(repo) / ref['repository_relative_directory']
    def pins():
        found = {}
        for name, pin in ref['files'].items():
            path = directory / name
            assert path.is_file() and not path.is_symlink()
            data = path.read_bytes()
            assert len(data) == pin['bytes'] and digest(data) == pin['sha256']
            found[name] = data
        return found
    files = pins()
    modules = [('basis', 'basis.py'), ('packet', 'packet.py'), ('_phase12_reader', 'review_saved.py')]
    old = {name: sys.modules.get(name) for name, _ in modules}
    bytecode = sys.dont_write_bytecode
    try:
        sys.dont_write_bytecode = True
        for name, filename in modules:
            spec = importlib.util.spec_from_file_location(name, directory / filename)
            module = importlib.util.module_from_spec(spec)
            sys.modules[name] = module
            spec.loader.exec_module(module)
        # Reuse the ancestor already validated by the exact phase12 reader.
        ancestor = []
        original_load = sys.modules['basis'].load
        def cached_load(path):
            assert Path(path).resolve() == Path(repo).resolve()
            if not ancestor:
                ancestor.append(original_load(path))
            return ancestor[0]
        sys.modules['basis'].load = cached_load
        checked = sys.modules['_phase12_reader'].review(directory, basis_repo=repo, repo=None)
        assert checked['status'] == 'PASS_SAVED_PHASE12' and not checked['current_sources_checked']
        assert len(ancestor) == 1
        previous, _, helper = ancestor[0]
        index = json.loads(files['index.json'])
        members = {}
        with tarfile.open(directory / 'execution.tar.gz', 'r:gz') as stream:
            for item in stream:
                sys.modules['packet'].safe(item.name)
                assert item.isfile() and item.name not in members
                data = stream.extractfile(item).read()
                assert index[item.name] == {'sha256': digest(data), 'bytes': len(data)}
                members[item.name] = data
        assert helper.manifest(members) == index
        data = {'member:' + name: value for name, value in members.items()}
        for path, route in json.loads(members['path-map.json']).items():
            value = (members if route['storage'] == 'packet' else previous)[route['key']]
            assert digest(value) == route['sha256'] and len(value) == route['bytes']
            data['path:' + path] = value
        assert pins() == files
        return data, checked, helper
    finally:
        sys.dont_write_bytecode = bytecode
        for name, value in old.items():
            if value is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = value
