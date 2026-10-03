"""Read-only offline replay in fresh external copies, normally and with -O.

Run python3 -B replay.py --output NEW_EXTERNAL_DIRECTORY.
The explicit --unsealed-payload mode is preliminary and cannot certify a release.
"""
import sys
sys.dont_write_bytecode = True
import argparse
import ast
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time
from verify_release import ROOT, require, inventory, check_pins, verify

COMMANDS = ('check_provenance.py','check_privacy.py','audit_dependency.py','check_entire_fiber.py','check_second_term.py','check_total_bitlength.py','check_total_bitlength_review.py')
BOOTSTRAP = r'''
import sys, runpy
from pathlib import Path
sys.dont_write_bytecode = True
try:
    import resource
except ImportError:
    resource = None
if resource is not None:
    resource.setrlimit(resource.RLIMIT_CPU,(240,240))
    resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
    resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,64*1024**2))
script = Path(sys.argv[1]).resolve()
sys.argv = [str(script)] + sys.argv[2:]
sys.path.insert(0,str(script.parent))
runpy.run_path(str(script),run_name='__main__')
'''


def prepare_output(output, root=ROOT):
    root = Path(root).resolve()
    if output is None:
        parent = Path(tempfile.gettempdir()).resolve()
        require(parent!=root and root not in parent.parents,'temporary output lies within release')
        return Path(tempfile.mkdtemp(prefix='report25-replay-'))
    path = Path(output).expanduser().absolute()
    for ancestor in (path,)+tuple(path.parents):
        require(not ancestor.is_symlink(),'symlink output path rejected')
    actual = path.resolve()
    require(actual!=root and root not in actual.parents,'output must be outside release')
    require(not path.exists(),'output already exists')
    require(path.parent.is_dir(),'output parent must already exist')
    path.mkdir()
    return path


def snapshot(root):
    files, directories = inventory(root)
    records = {}
    for name, path in files.items():
        info = path.stat()
        records[name] = (info.st_size,sha256(path.read_bytes()).hexdigest(),info.st_mode,info.st_mtime_ns)
    dirs = {name:((Path(root)/name).stat().st_mode,(Path(root)/name).stat().st_mtime_ns) for name in directories}
    info = Path(root).stat()
    return records, dirs, (info.st_mode,info.st_mtime_ns)


def check_runtime_dependencies(root):
    require(hasattr(sys,'stdlib_module_names'),'Python 3.10 or newer is required')
    files, unused = inventory(root)
    local = {Path(name).stem for name in files if '/' not in name and name.endswith('.py')}
    imports = set()
    for name,path in files.items():
        if not name.endswith('.py'):
            continue
        require('/' not in name,'unexpected executable source subdirectory')
        for node in ast.walk(ast.parse(path.read_text(encoding='utf-8'),filename=name)):
            if isinstance(node,ast.Import):
                imports.update(alias.name.split('.')[0] for alias in node.names)
            elif isinstance(node,ast.ImportFrom):
                require(node.level==0,'relative code import is not allowed')
                imports.add((node.module or '').split('.')[0])
    require(imports <= sys.stdlib_module_names | local,'non-standard-library dependency found')
    return sorted(imports-local)


def run_script(root, script, optimized, log):
    cmd = [sys.executable,'-I','-S','-B']+(['-O'] if optimized else [])+['-c',BOOTSTRAP,str(root/script)]
    environment = {k:v for k,v in os.environ.items() if not k.startswith('PYTHON')}
    environment['TMPDIR'] = str(log.parent)
    started = time.monotonic()
    # A distinct unrelated working directory tests path portability.
    with log.open('wb') as out:
        completed = subprocess.run(cmd,cwd=log.parent,env=environment,stdout=out,stderr=subprocess.STDOUT,timeout=300)
    require(completed.returncode==0,'script failed: '+script+'; inspect external replay log '+str(log))
    return {'script':script,'optimized':optimized,'returncode':completed.returncode,'seconds':round(time.monotonic()-started,3),'isolated':True,'site_packages_disabled':True}


def replay(output=None, root=ROOT, unsealed=False):
    root = Path(root).absolute()
    before = snapshot(root)
    integrity = check_pins(root) if unsealed else verify(root)
    imports = check_runtime_dependencies(root)
    output = prepare_output(output,root)
    runs = []
    for optimized in (False,True):
        mode = 'optimized' if optimized else 'normal'
        copy = output/mode
        shutil.copytree(root,copy)
        logs = output/(mode+'-logs')
        logs.mkdir()
        require(snapshot(copy)==before,'initial relocated copy differs')
        commands = COMMANDS if unsealed else ('verify_release.py',)+COMMANDS+('release_checks.py','verify_release.py')
        for index,script in enumerate(commands):
            runs.append(run_script(copy,script,optimized,logs/(str(index).zfill(2)+'.log')))
            require(snapshot(copy)==before,'copied release files, directories, bytes, modes or mtimes changed')
            require(snapshot(root)==before,'original release files, directories, bytes, modes or mtimes changed')
    integrity = check_pins(root) if unsealed else verify(root)
    require(snapshot(root)==before,'original release changed before completion')
    receipt = {'status':'PASS','scope':'preliminary unsealed scientific payload only' if unsealed else 'complete sealed release',
               'python':sys.version.split()[0],'modes':['normal','optimized'],'scripts':runs,
               'scientific_subprocesses':len(COMMANDS)*2,'integrity':integrity,
               'standard_library_imports':imports,'third_party_runtime_dependencies':[],
               'whole_original_and_relocated_releases_unchanged':True,
               'invariance_fields':['file inventory','directory inventory','bytes','file modes','modification times'],
               'negative_integrity_tests':'not run; final seal unavailable' if unsealed else 'passed in normal and optimized modes',
               'source_repository_python_executed':False,'complete_padded_native_witness_materialized':False,
               'finite_examples_are_auxiliary_only':True}
    (output/'replay-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    return receipt


if __name__=='__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    parser.add_argument('--unsealed-payload',action='store_true')
    args = parser.parse_args()
    print(json.dumps(replay(args.output,unsealed=args.unsealed_payload),indent=2))
