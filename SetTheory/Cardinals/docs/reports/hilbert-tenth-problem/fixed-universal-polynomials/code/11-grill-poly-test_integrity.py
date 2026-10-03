#!/usr/bin/env python3
"""Adversarial missing/extra/tamper tests against disposable package copies."""
import sys
sys.dontwritebytecode = True
import json
from pathlib import Path
import shutil
import tempfile
import replay

ROOT = Path(__file__).resolve().parent

def flip(p):
    with p.open('r+b') as f:
        offset = max(0, p.stat().st_size // 2)
        f.seek(offset)
        b=f.read(1)
        if not b:
            raise RuntimeError('Cannot mutate empty fixture')
        f.seek(offset)
        f.write(bytes([b[0] ^ 1]))

def main():
    replay.verify_inventory()
    cases = [
        ('literal data mutation', 'frozen/input-research/literal/literal_tables.json', 'flip'),
        ('inert upstream source mutation', 'frozen/input-research/literal/upstream_u15_builder.py.txt', 'flip'),
        ('local executable mutation', 'replay_code/arithmetic/compact_dag.py', 'flip'),
        ('full DAG mutation', 'frozen/arithmetic/universal.dag', 'flip'),
        ('scientific manifest mutation', 'frozen/arithmetic/universal.json', 'flip'),
        ('inventory manifest mutation', 'INVENTORY.json', 'flip'),
        ('inventory root digest mutation', 'INVENTORY.sha256', 'flip'),
        ('missing theorem source', 'frozen/arithmetic/FULL_COMPOSITION_PROOF.md', 'remove'),
        ('extra undeclared file', 'undeclared.txt', 'add'),
        ('extra empty directory', 'undeclared-directory', 'mkdir'),
        ('forbidden stale cache', '__pycache__/extra.pyc', 'add'),
    ]
    results=[]
    with tempfile.TemporaryDirectory(prefix='grill-integrity-tests-') as temp:
        for title,relative,mutation in cases:
            target=Path(temp)/'package'
            shutil.copytree(ROOT,target)
            p=target/relative
            if mutation=='flip':flip(p)
            elif mutation=='remove':p.unlink()
            elif mutation=='mkdir':p.mkdir()
            else:
                p.parent.mkdir(parents=True,exist_ok=True);p.write_text('undeclared data\n')
            try:
                replay.verify_inventory(target)
            except (RuntimeError, ValueError, OSError) as error:
                results.append({'case':title,'status':'REJECTED','reason':str(error)})
            else:
                raise RuntimeError('Mutation unexpectedly accepted: '+title)
            shutil.rmtree(target)
    replay.verify_inventory()
    print(json.dumps({'status':'PASS_ADVERSARIAL_INTEGRITY','optimized':bool(sys.flags.optimize),'cases':results},indent=2,sort_keys=True))

if __name__ == '__main__':
    main()
