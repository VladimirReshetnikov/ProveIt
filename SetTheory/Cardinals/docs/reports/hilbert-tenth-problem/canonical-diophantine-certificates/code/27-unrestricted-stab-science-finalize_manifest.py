#!/usr/bin/env python3
"""Hash only this new packet; read old dependency files as inert bytes."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    files={str(p.relative_to(ROOT)):sha(p) for p in sorted(ROOT.rglob('*'))
           if p.is_file() and p.name!='manifest.json' and '__pycache__' not in p.parts}
    dependency_root=ROOT.parent/'sandpile-fixed-arity-20261004'
    dependencies={str(p):sha(p) for p in (
        dependency_root/'PROOF.md',dependency_root/'sources/pell-source.lean',
        ROOT.parent/'sandpile-repeated-target-20261004/ARCHITECTURE.md')}
    receipt=dict(status='FINAL_PACKET_HASHES',files=files,dependencies=dependencies,
        theorem='Finite legal global stabilization with unrestricted multiplicities on the unchanged raw eight-field physical input',
        positive_witnesses=3262,equalities=1897,gates=14571,exact_degree=18,
        dag_sha256=files['evidence/polynomial-dag.json'],
        caveat='Constructive Pell theorem is an explicit inherited dependency; no full giant Pell witness, upstream program, schedule, Lean, article, target-firing, finite-fold, real-exactness or computability-corollary claim.')
    (ROOT/'evidence/manifest.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'files_hashed':len(files),'dag_sha256':receipt['dag_sha256']},indent=2))

if __name__=='__main__':main()
