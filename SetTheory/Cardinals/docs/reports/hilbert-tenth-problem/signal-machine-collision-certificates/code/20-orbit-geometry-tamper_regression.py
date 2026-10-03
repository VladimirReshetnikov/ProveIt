#!/usr/bin/env python3
"""Six bounded tests of trusted preflight; altered scientific code is never run."""
from pathlib import Path
import hashlib,json,shutil,subprocess,tempfile
ROOT=Path(__file__).resolve().parent

def reseal(root):
    entries=[]
    for p in sorted(root.rglob('*')):
        if p.is_file() and not p.is_symlink() and p.relative_to(root).as_posix()!='SHA256SUMS':
            entries.append(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(root).as_posix())
    (root/'SHA256SUMS').write_text('\n'.join(entries)+'\n')

def run(root):
    return subprocess.run(['sh',str(root/'reproduce.sh'),'--verify-only'],cwd=root.parent,text=True,capture_output=True)

cases=('changed_science','resealed_changed_science','resealed_missing_required_script','resealed_boolean_receipt','extra_payload','symlink_payload')
results={}
with tempfile.TemporaryDirectory(prefix='report30-tamper-') as tmp:
    for name in cases:
        target=Path(tmp)/name
        shutil.copytree(ROOT,target,copy_function=shutil.copy2)
        script=target/'scientific/geometry/audit.py'
        if name in ('changed_science','resealed_changed_science'):
            script.write_text(script.read_text()+'\nraise RuntimeError("tampered source executed")\n')
        elif name=='resealed_missing_required_script':
            script.unlink()
        elif name=='resealed_boolean_receipt':
            p=target/'verification/expected-geometry.json'
            receipt=json.loads(p.read_text());receipt['schema_version']=True
            p.write_text(json.dumps(receipt,indent=2)+'\n')
        elif name=='extra_payload':
            (target/'unexpected.txt').write_text('unexpected payload\n')
        else:
            script.unlink();script.symlink_to(ROOT/'scientific/geometry/audit.py')
        if name.startswith('resealed_'):
            reseal(target)
        result=run(target)
        if result.returncode==0:
            raise RuntimeError('Tamper accepted: '+name)
        if 'tampered source executed' in result.stderr:
            raise RuntimeError('Altered scientific code executed')
        if 'Preflight rejected:' not in result.stderr:
            raise RuntimeError('Failure did not come from preflight: '+name+' '+result.stderr)
        results[name]='REJECTED_BEFORE_HELPER_EXECUTION'
clean=run(ROOT)
if clean.returncode:
    raise RuntimeError('Clean preflight failed: '+clean.stderr)
print(json.dumps({'status':'PASS','cases':results,'clean_inventory':'PASS'},indent=2,sort_keys=True))
