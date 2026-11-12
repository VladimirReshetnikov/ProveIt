"""Replay concrete certificates and whole-program source measurements offline."""
from pathlib import Path
import argparse
import ast
import hashlib
import importlib.util
import json
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent

def require(condition, message):
    if not condition:
        raise ValueError(message)

def run(path):
    process = subprocess.run([sys.executable,str(ROOT/path)],cwd=ROOT,text=True,
                             stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    require(process.returncode == 0, path+'\n'+process.stdout[-8000:])
    return {'script':path,'exit_code':process.returncode}

def verify_manifest(distribution_integrity=False):
    manifest = ROOT/'MANIFEST.json'
    if distribution_integrity:
        require(manifest.is_file(),'Distribution integrity requires MANIFEST.json')
    if manifest.exists():
        inventory = json.loads(manifest.read_text())
        groups = ['source_files'] + (['generated_files'] if distribution_integrity else [])
        for group in groups:
            entries = inventory[group]
            require(isinstance(entries,dict),'Manifest '+group+' must map paths to SHA-256 hashes')
            for path, digest in entries.items():
                file = (ROOT/path).resolve()
                require(file.is_relative_to(ROOT.resolve()),'Manifest path outside package: '+path)
                require(file.is_file(),'Missing '+group+' file: '+path)
                require(hashlib.sha256(file.read_bytes()).hexdigest()==digest,
                        'Changed '+group+' file: '+path)

def write_normalized_kernel(measure):
    source = (ROOT/'code/kernel.py').read_bytes().decode('utf-8')
    tree = ast.fix_missing_locations(measure.StripDocstrings().visit(ast.parse(source)))
    data = (ast.unparse(tree)+'\n').encode('utf-8')
    path = 'code/kernel_normalized.py'
    (ROOT/path).write_bytes(data)
    return {'path':path,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--distribution-integrity',action='store_true',
                        help='also check the distributed hashes of generated files before replaying tests')
    args = parser.parse_args()
    verify_manifest(args.distribution_integrity)

    steps = [run('code/validate.py'),run('code/check_opening.py'),
             run('scripts/check_seed_shift.py')]
    spec = importlib.util.spec_from_file_location('source_measure',ROOT/'scripts/source_measure.py')
    measure = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(measure)
    programs = ['reference/published_tokens.py','reference/published_structure.py',
                'reference/published_bytes.py','reference/published_762.py',
                'code/kernel.py','code/kernel_unpacked.py']
    rows = [{'path':p,**measure.metrics(ROOT/p)} for p in programs]
    by_path = {r['path']:r for r in rows}
    old = by_path['reference/published_762.py']
    new = by_path['code/kernel.py']
    require(new['normalized_bytes']<old['normalized_bytes'],
            'The strict normalized-byte comparison did not reproduce on this Python version')
    require(new['sha256']=='f1e11d165890303162ddfcb8da4ce8430ad935303c78d3063212939c517a5fb4',
            'Unexpected main checker version')
    normalized = write_normalized_kernel(measure)
    require(normalized['bytes']==new['normalized_bytes'],
            'Generated executable differs from the inherited normalization measurement')
    metrics = {'python':platform.python_version(),'programs':rows,
               'published_envelope':{
                   k:min(by_path[p][k] for p in programs[:4])
                   for k in ('normalized_tokens','ast_nodes','normalized_bytes')},
               'new_byte_saving':old['normalized_bytes']-new['normalized_bytes']}
    (ROOT/'evidence/metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
    result = {'python':platform.python_version(),'steps':steps,
              'main_kernel':{k:new[k] for k in ('normalized_tokens','ast_nodes','normalized_bytes','sha256')},
              'normalized_kernel':normalized,
              'published_byte_leader':old['normalized_bytes'],
              'byte_saving':old['normalized_bytes']-new['normalized_bytes'],
              'certificates':json.loads((ROOT/'code/validation.json').read_text()),
              'opening':json.loads((ROOT/'code/opening_validation.json').read_text()),
              'countdown':json.loads((ROOT/'evidence/seed_shift_finite_checks.json').read_text())}
    (ROOT/'evidence/reproduction.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'python':result['python'],'main_kernel':result['main_kernel'],
                      'published_envelope':metrics['published_envelope'],
                      'byte_saving':result['byte_saving'],
                      'fixtures':result['certificates']['fixtures'],
                      'status':'all supplied checks passed'},indent=2))

if __name__ == '__main__':
    main()
