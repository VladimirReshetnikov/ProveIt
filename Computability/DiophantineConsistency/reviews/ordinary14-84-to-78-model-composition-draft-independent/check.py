#!/usr/bin/env python3
"""Independent source-interface/receipt review; no Lean invocation."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

D=Path(__file__).resolve().parents[2]
A=D/'research/ordinary14-84-to-78-model-composition-draft'
def sha(data):return hashlib.sha256(data).hexdigest()
def pinned(path,expected):
    data=path.read_bytes()
    assert sha(data)==expected,str(path)
    return data
source=pinned(A/'ModelComposition.lean','5d1fbd9bdf67df9d9c2c2a6d139d6decbd69753c6945dd4ca70dfff024eec84e').decode()
readme=(A/'README.md').read_bytes()
tail=(b'\nIndependent source review is recorded in\n'
      b'`../../reviews/ordinary14-84-to-78-model-composition-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)])=='276652270725f55562ce72d75cbef287a96ff679e672109a16e33072b282e1ee'
first=pinned(D/'research/ordinary14-direct-first-root-positive-client-draft/PositiveClient.lean',
             '888f0d0641246eedfdcafdffafa32d0986a46a5db4106196b20e7e48472aeda3').decode()
second=pinned(D/'research/ordinary14-aux-graph-equivalence-draft/AuxGraphEquivalence.lean',
              '57caf3a86a1caf93828331c3775d14e13929a9427d3e8b981398a40d1fee84ea').decode()
for text in ('theorem positive_zero_iff (p : Fin 4 → ℤ) (beta : V)',
             '(hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)',
             'P84QcubeGraph.graph p','P78AuxRoot.graph p',
             'DirectFirstRootPositiveClientDraft.positive_zero_iff p beta hbeta hport',
             'AuxGraphEquivalenceDraft.positive_zero_iff p beta hbeta hport',
             'theorem positive_zero_iff_natural_ports (p : Fin 4 → ℕ)',
             'DirectFirstRootPositiveClientDraft.positive_zero_iff_natural_ports p hbeta',
             'AuxGraphEquivalenceDraft.positive_zero_iff_natural_ports p hbeta'):
    assert text in source,text
for text in ('P84QcubeGraph.graph p','P79DirectPell.graph p',
             '(hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)',
             'theorem positive_zero_iff_natural_ports (p : Fin 4 → ℕ)'):
    assert text in first,text
for text in ('P79DirectPell.graph p','P78AuxRoot.graph p',
             '(hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta)',
             'theorem positive_zero_iff_natural_ports (p : Fin 4 → ℕ)'):
    assert text in second,text

def replay(path,receipt):
    run=subprocess.run([sys.executable,'-I','-S','-B',str(path)],cwd=D,
                       stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120,check=True)
    assert not run.stderr and run.stdout==receipt.read_bytes()
replay(A/'check_source.py',A/'observation.json')
for name in ('ordinary14-direct-first-root-positive-client-draft-independent',
             'ordinary14-aux-graph-equivalence-draft-independent'):
    packet=D/'reviews'/name
    replay(packet/'check.py',packet/'result.json')
print(json.dumps({'scope':'source interface/receipt review only; no Lean or model theorem',
                  'author_readme_prelink_sha256':sha(readme[:-len(tail)]),
                  'middle_graph':'P79DirectPell.graph p',
                  'shared_beta_hypotheses':True,'natural_port_specializations_match':True,
                  'component_reviews_replayed':2},sort_keys=True,indent=2))
