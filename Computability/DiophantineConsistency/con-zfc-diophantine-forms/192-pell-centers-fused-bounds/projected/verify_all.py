#!/usr/bin/env python3
"""Replay the frozen immediate parent and all new finite checks offline."""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile,zipfile

ROOT=Path(__file__).resolve().parent
ARCHIVE_HASH='f18a92527300eee08a6e3d0c4a0ee38f2156bffabc5dfbf2f418e50ae72a521b'
def run(path,cwd):
    cmd=[sys.executable,'-B']
    if sys.flags.optimize:cmd.append('-O')
    cmd.append(str(path))
    r=subprocess.run(cmd,cwd=cwd,capture_output=True,text=True)
    if r.returncode:raise RuntimeError(r.stderr or r.stdout)
    return json.loads(r.stdout)
def main():
    archive=ROOT/'sources/parent_archive.zip'
    if hashlib.sha256(archive.read_bytes()).hexdigest()!=ARCHIVE_HASH:raise ValueError('Parent archive binding')
    with tempfile.TemporaryDirectory(prefix='conzfc-guard-parent-') as t:
        t=Path(t)
        with zipfile.ZipFile(archive) as z:
            for n in z.namelist():
                if not (t/n).resolve().is_relative_to(t.resolve()):raise ValueError('Archive path escapes extraction')
            z.extractall(t)
        parent=t/'ConZFC_Direct_Integer_Elimination_2026-10-25'
        bindings=[('source/anchor219.json','anchor219.json'),('joint209.json','joint209.json')]
        bindings += [('equations/'+p.name,p.name) for p in (ROOT/'sources').glob('integer*_degree*.json') if not p.name.endswith('_linear.json')]
        for a,b in bindings:
            if (parent/a).read_bytes()!=(ROOT/'sources'/b).read_bytes():raise ValueError('Immediate parent source copy differs: '+b)
        parent_receipt=run(parent/'verify.py',parent)
    receipts={name:run(ROOT/'code'/name,ROOT) for name in ['verify_orientation_seed.py','verify_orientation_projection.py','verify.py']}
    print(json.dumps({'status':'pass','python_optimized':bool(sys.flags.optimize),
        'parent_archive_sha256':ARCHIVE_HASH,'parent_source_bindings':len(bindings),
        'parent_replay':parent_receipt,'new_checks':receipts,
        'scope':'Finite replay of the exact source/polynomial chain. Unbounded theorems are separately proved; no consistency decision.'},sort_keys=True,indent=2))
if __name__=='__main__':main()
