#!/usr/bin/env python3
"""Rebuild and audit the component in a temporary directory, preserving its bytes."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:raise RuntimeError(message)

def main():
    source=json.loads((ROOT/'SOURCE_FILES.json').read_text())
    for item in source['files']:
        data=(ROOT/item['path']).read_bytes();require(len(data)==item['bytes'] and hashlib.sha256(data).hexdigest()==item['sha256'],'pinned source mismatch: '+item['path'])
    if (ROOT/'SHA256SUMS.json').exists():
        for name,want in json.loads((ROOT/'SHA256SUMS.json').read_text()).items():require(hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==want,'release hash: '+name)
    runs=[]
    with tempfile.TemporaryDirectory(prefix='proveit-free-carrier-') as temp:
        work=Path(temp)/'component';shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        for optimize,script in [(False,'build.py'),(False,'materialize.py'),(False,'verify_core.py'),(True,'verify_core.py')]:
            cmd=[sys.executable]+(['-O'] if optimize else [])+[script]
            cp=subprocess.run(cmd,cwd=work,text=True,capture_output=True)
            require(cp.returncode==0,'audit failed: '+script+'\n'+cp.stdout+'\n'+cp.stderr)
            runs.append({'script':script,'optimized_python':optimize,'status':'passed'})
        compared=0
        for subdir in ['generated','fixed']:
            for original in (ROOT/subdir).rglob('*'):
                if original.is_file() and original.suffix!='.pyc':
                    other=work/original.relative_to(ROOT);require(other.exists() and original.read_bytes()==other.read_bytes(),'rebuild mismatch: '+str(original.relative_to(ROOT)));compared+=1
        # Authenticate every materialized leaf against the complete four-port recipe.
        from materialize import leaf_values
        import gzip
        body=json.loads((ROOT/'generated/calibrated_absorbed_positive.json').read_text());manifest=json.loads((ROOT/'fixed/MANIFEST.json').read_text());records={r['name']:r for r in manifest['leaves']}
        for name,z in leaf_values(body):
            rec=records[name];raw=gzip.decompress((ROOT/rec['path']).read_bytes());actual=int.from_bytes(raw[1:],'little')*(-1 if raw[0] else 1)
            require(actual==z and hashlib.sha256(raw).hexdigest()==rec['sha256'],'materialized fixed leaf mismatch: '+name)
    receipt={'status':'passed','source_files':len(source['files']),'byte_identical_rebuilt_files':compared,'runs':runs,'primary':{'positive_variables':9,'degree':4686812,'operations':560,'live_fixed_leaves':15},'proof_status':'Finite algebraic and implementation checks. The universal solvability proof is mathematical and imports the explicitly identified compiler/calibration and Jones ratio theorems.'}
    (ROOT/'VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
