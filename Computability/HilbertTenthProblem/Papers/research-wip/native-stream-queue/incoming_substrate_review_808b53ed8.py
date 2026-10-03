"""Reproduce the seven-report 808b53ed8/48ee077c7 substrate review.

Original archives remain unchanged. Removed archives can be recovered from
their arrival commits. Helpers execute only explicitly pinned original or
patched source bytes in private directories. Run without Python -O.
"""
import argparse
from contextlib import contextmanager
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import stat
import subprocess
import sys
import tempfile
import types
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[5]
HERE = Path(__file__).resolve().parent
ARCHIVES = {
    'Collision_Geometry_Diophantine_Signal_Machines.zip':
        ('808b53ed8', '584bfaadc7ba69ee97fcf2339190632fa0e4ba82a5ebb70cb3dbd5caebdd5f04', 'collision_geometry'),
    'Signal_Machine_Diophantine_Certificates.zip':
        ('808b53ed8', '288d8f9790748ab0dde812bf8f770758306ac78ec1a0a04c75499245471d9ca1', 'signal-diophantine-release'),
    'Maximal_Parallel_Diophantine.zip':
        ('808b53ed8', 'e6a3dcfc419f2fb49552d5c4d0a17959f4360b9610799ef8190a27a2938a8066', 'Maximal_Parallel_Diophantine'),
    'Order_Is_Not_a_Moment.zip':
        ('808b53ed8', '2cd366ff60ac48dfb6138a00871cc32ae4bd6f6778ddac2a590cd1559664aacc', 'order_is_not_a_moment'),
    'ProveIt_Exact_Convergence_Research.zip':
        ('808b53ed8', '6e943e3301e5641b2306eff1cf979702a2584481c430d5561eed1c055b16a0ec', 'Exact_Convergence_Research'),
    'Total_Quadratic_Diophantine_Semantics.zip':
        ('808b53ed8', '5b9fe27c520a2a1eeee14f197d8d62ffe9ff180c72ce7b6ee5645ddfc2f74c9b', 'total_quadratic_semantics'),
    'ProveIt_Affine_Matrix_Diophantine_Research.zip':
        ('48ee077c7', '3a6c1bff56b913b8376f2c8fa1cf5bf3cd4529341d3f5a29606f08d2728ccea2', 'Affine_Matrix_Diophantine_Research'),
}
RUNS = {
    'Collision_Geometry_Diophantine_Signal_Machines.zip': [['code/run_checks.py']],
    'Signal_Machine_Diophantine_Certificates.zip': [['scripts/run_replay.py']],
    'Maximal_Parallel_Diophantine.zip': [['code/verify.py']],
    'Order_Is_Not_a_Moment.zip': [['code/verify.py']],
    'ProveIt_Exact_Convergence_Research.zip': [['code/run_checks.py']] + [
        ['code/check_certificate.py', f'artifacts/{name}_certificate.json',
         '--game', f'artifacts/{name}_game.json'] for name in ('small','countdown','fixedpoint')],
    'Total_Quadratic_Diophantine_Semantics.zip': [['code/test_compiler.py'], ['code/verify_exports.py']],
    'ProveIt_Affine_Matrix_Diophantine_Research.zip': [['verify.py']],
}
HELPERS = {
    'signals': ('incoming_signal_checks_808b.py', 'e0ae8f17c7c0f7d7d9a97095a4d508957ac7a98a8d97a11b5fd804652cca0a6a'),
    'affine': ('affine_matrix_square_projection_review808b.py', '5b95fb4ec506feafe820ee94c575dd5275ae22bf85df9a4e95ab3e8c454e7c5d'),
    'convergence_repairs': ('incoming_convergence_repair_checks_808b.py', 'd231636dd81dd5de32f99b2d135878e922628332d2bf075e407e2bd7e0f13532'),
    'parallel_order': ('incoming_parallel_order_checks_808b.py', 'f69793fa4283251e7a4d0ce07dbcf79f461db4f954079a5eca4e9c75fb4affa9'),
    'parallel_repair': ('incoming_maximal_parallel_repair_checks_808b.py', '4f2203cf20fc9bf5649b7ec6b97218e8403e58bdae634268de24e92cf26798e5'),
    'convergence': ('incoming_convergence_checks_808b.py', '63b6744376bcf2cec81f8b06879d538926a430b56769653e52cca6c43a78fe25'),
    'convergence_scale': ('incoming_convergence_scale_checks_808b.py', 'c980fcc8c3967b3ee265f5b07f841799d2be0c1c7e2264d32642cd0f2188cbdf'),
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def archive(name, *, from_git=False):
    if type(name) is not str or name not in ARCHIVES or type(from_git) is not bool:
        raise ValueError('Unknown archive or invalid source flag')
    commit, digest, prefix = ARCHIVES[name]
    path = ROOT/'docs'/'incoming'/name
    raw = path.read_bytes() if path.exists() and not from_git else subprocess.run(
        ['git','show',f'{commit}:docs/incoming/{name}'], cwd=ROOT,
        check=True, capture_output=True).stdout
    if sha(raw) != digest: raise ValueError('Archive hash mismatch')
    out = {}
    with ZipFile(io.BytesIO(raw)) as z:
        if len(z.namelist()) != len(set(z.namelist())): raise ValueError('Duplicate ZIP member')
        for item in z.infolist():
            p = PurePosixPath(item.filename)
            if (p.is_absolute() or '..' in p.parts or '\\' in item.filename
                    or not p.parts or p.parts[0] != prefix
                    or stat.S_ISLNK(item.external_attr >> 16)):
                raise ValueError('Unsafe ZIP member')
            if not item.is_dir(): out[item.filename] = z.read(item)
    return out


def extract(files, root):
    for member, raw in files.items():
        path = root/member
        if not path.resolve().is_relative_to(root.resolve()): raise ValueError('Unsafe member')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)


def metadata_normalized(value):
    """Only top-level runtime/environment fields of author receipts are ignored."""
    if type(value) is dict:
        return {k:v for k,v in value.items() if k not in
            ('runtime_seconds','elapsed_seconds','python','python_version')}
    return value


def original_replays(all_files):
    result = {}
    for name, files in all_files.items():
        with tempfile.TemporaryDirectory(prefix='substrate-808b-author-') as tmp:
            root = Path(tmp); extract(files,root)
            package = root/ARCHIVES[name][2]
            runs = []
            for argv in RUNS[name]:
                done = subprocess.run([sys.executable]+argv,cwd=package,
                    capture_output=True,text=True,timeout=300)
                assert done.returncode == 0, (name,argv,done.stdout,done.stderr)
                try: summary = metadata_normalized(json.loads(done.stdout))
                except json.JSONDecodeError: summary = None
                runs.append(dict(argv=argv,exit_code=done.returncode,json_summary=summary))
            comparisons = {}
            for member, old in files.items():
                if not member.endswith('.json'): continue
                fresh = (root/member).read_bytes()
                a, b = json.loads(old), json.loads(fresh)
                assert metadata_normalized(a) == metadata_normalized(b), (name,member)
                ignored = sorted(set(a) | set(b)) if type(a) is dict and type(b) is dict else []
                ignored = [k for k in ignored if k in
                    ('runtime_seconds','elapsed_seconds','python','python_version')]
                # A reproducibility receipt must not depend on whether this
                # host happens to match the author's Python version or timing.
                if not ignored: assert old == fresh, (name,member,'nonmetadata bytes changed')
                comparisons[member] = dict(comparison='normalized_json' if ignored else 'identical_bytes',
                    ignored_metadata_fields=ignored,
                    normalized_sha256=sha(json.dumps(metadata_normalized(b),sort_keys=True).encode()))
            result[name] = dict(runs=runs, existing_json_replays=comparisons)
    return result


@contextmanager
def helper(which):
    filename, digest = HELPERS[which]
    path = HERE/filename; raw = path.read_bytes()
    if sha(raw) != digest: raise ValueError('Review helper hash mismatch')
    name = '_substrate808b_'+which; missing = object()
    old = sys.modules.get(name,missing)
    module = types.ModuleType(name); module.__file__ = str(path)
    sys.modules[name] = module
    try:
        exec(compile(raw,str(path),'exec'),module.__dict__)
        yield module
    finally:
        if old is missing: sys.modules.pop(name,None)
        else: sys.modules[name] = old


def independent_checks(all_files):
    with tempfile.TemporaryDirectory(prefix='substrate-808b-independent-') as tmp:
        root = Path(tmp)
        for files in all_files.values(): extract(files,root)
        result = {}
        with helper('signals') as h:
            result['signals'] = h.verify(root/'collision_geometry', root/'signal-diophantine-release')
        with helper('affine') as h:
            result['affine'] = h.run(root/'Affine_Matrix_Diophantine_Research')
        with helper('convergence') as h:
            result['convergence'] = h.verify(root/'Exact_Convergence_Research',root/'total_quadratic_semantics')
        with helper('convergence_repairs') as h:
            result['convergence_repairs'] = h.verify(root/'Exact_Convergence_Research',
                root/'total_quadratic_semantics', HERE/'exact_convergence_input_binding.patch',
                HERE/'total_quadratic_immutable_inputs.patch')
            # Test both Bellman repairs together as well as the separate input
            # checker/irreversible-catalogue regression above. The scale helper
            # makes its own private copy and runs the entire author suite.
            composed = root/'composed'
            extract(all_files['ProveIt_Exact_Convergence_Research.zip'],composed)
            package = composed/'Exact_Convergence_Research'
            patch = HERE/'exact_convergence_input_binding.patch'
            assert sha(patch.read_bytes()) == h.PINS['bellman_patch']
            done = subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(patch)],
                cwd=package,capture_output=True,text=True,timeout=300)
            assert done.returncode == 0, (done.stdout,done.stderr)
            checker_hash = sha((package/'code/check_certificate.py').read_bytes())
            assert checker_hash == h.PINS['patched_bellman_checker']
        with helper('convergence_scale') as h:
            result['convergence_scale'] = h.verify(package,HERE/'exact_convergence_integer_scale.patch')
            result['convergence_scale']['composed_checker_sha256'] = checker_hash
        result['parallel_order'] = helper_cli('parallel_order', [
            '--parallel-root',str(root/'Maximal_Parallel_Diophantine'),
            '--order-root',str(root/'order_is_not_a_moment')],root)
        result['parallel_repair'] = helper_cli('parallel_repair', [
            '--original-root',str(root/'Maximal_Parallel_Diophantine'),
            '--patch',str(HERE/'maximal_parallel_immutable_guards.patch')],root)
        return result


def helper_cli(which, argv, root):
    filename, digest = HELPERS[which]
    path = HERE/filename
    if sha(path.read_bytes()) != digest: raise ValueError('Review helper hash mismatch')
    receipt = root/(which+'.json')
    done = subprocess.run([sys.executable,str(path)]+argv+['--receipt',str(receipt)],
        cwd=root,capture_output=True,text=True,timeout=600)
    assert done.returncode == 0, (which,done.stdout,done.stderr)
    return json.loads(receipt.read_text())


def run():
    files = {name:archive(name) for name in ARCHIVES}
    assert all(archive(name,from_git=True) == files[name] for name in ARCHIVES)
    members = {name:{member:dict(bytes=len(raw),sha256=sha(raw)) for member,raw in data.items()}
        for name,data in files.items()}
    return dict(status='PASS', archive_arrivals_and_sha256=ARCHIVES,
        archive_members=members, git_fallbacks_checked=len(files),
        review_source_sha256=sha(Path(__file__).read_bytes()),
        helpers=HELPERS, originals=original_replays(files), independent=independent_checks(files),
        scope='Finite exact checks and reviewed proofs; corrected implementations are separate patches; no universal operation improvement.')


if __name__ == '__main__':
    if not __debug__: raise RuntimeError('Assertions must be enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args = parser.parse_args()
    result = run(); path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result,indent=2)+'\n')
    else: assert json.loads(path.read_text()) == json.loads(json.dumps(result)), 'review receipt mismatch'
    print(json.dumps(dict(status='PASS',archives=len(ARCHIVES),
        author_commands=sum(map(len,RUNS.values())),git_fallbacks=len(ARCHIVES),
        receipt=str(path)),indent=2))
