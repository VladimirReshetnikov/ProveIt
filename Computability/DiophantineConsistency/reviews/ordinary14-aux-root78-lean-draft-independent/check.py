#!/usr/bin/env python3
"""Independent literal source comparison; never invokes Lean."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

D=Path(__file__).resolve().parents[2]
A=D/'research/ordinary14-aux-root78-lean-draft'
P=D/'research/ordinary14-aux-root78'
def sha(data): return hashlib.sha256(data).hexdigest()
def pinned(path, expected):
    data=path.read_bytes()
    assert sha(data)==expected, str(path)
    return data
source=pinned(A/'P78AuxRoot.lean','1a412f13645a0c5c91554b71ee67e24e34ab968bf69575292eaf43225a52d9f7').decode()
candidate=json.loads(pinned(P/'candidate.json','d579ba32a40eed91a336b0015086104e1d1a7c6569092f757328769a3128ab43'))
readme=(A/'README.md').read_bytes()
tail=(b'\nIndependent source review is recorded in\n'
      b'`../../reviews/ordinary14-aux-root78-lean-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)])=='94ed138e7aae122979d728349747cd83386e40371886e3c8badec4a6763ea0c5'
assert len(candidate['source'])==78
for i,name in enumerate(candidate['witnesses']):
    assert f'let {name} : Expr (Fin 14) := .var {i}' in source
for i,name in enumerate(candidate['fixed_numerals']):
    assert f'let {name} : Expr (Fin 14) := .constant (p {i})' in source
block=source.split('  -- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0]
assert block==''.join(f'  let {n} := {a} {op} {b}\n' for n,op,a,b in candidate['source'])
assert '⟨A0, A1, Fa, g72, guard, guarded_out⟩' in source
assert 'theorem output_shape' in source

def replay(path, argv, receipt):
    run=subprocess.run([sys.executable,'-I','-S','-B',str(path),*argv],cwd=D,
                       stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120,check=True)
    assert not run.stderr and run.stdout==receipt.read_bytes()
replay(A/'make_graph.py',['--check'],A/'observation.json')
replay(P/'check.py',[],P/'result.json')
print(json.dumps({'scope':'literal source and external checks only; no Lean or file theorem',
                  'author_readme_prelink_sha256':sha(readme[:-len(tail)]),
                  'literal_rows':78,'slot8':candidate['witnesses'][8],
                  'slot11':candidate['witnesses'][11],'source_generator_replayed':True,
                  'candidate_checker_replayed':True},sort_keys=True,indent=2))
