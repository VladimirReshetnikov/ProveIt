#!/usr/bin/env python3
from pathlib import Path
import importlib.util,json,hashlib
R=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('f',R/'build_marker_family.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
C=R/'marker_family/novelty_corpus';manifest=json.loads((C/'manifest.json').read_text());keys=set()
for row in manifest['representatives']:
 p=C/row['file'];assert m.sha(p)==row['sha256'];st,T=m.parse(p);key=m.canonical(T,st)
 assert hashlib.sha256(repr(key).encode()).hexdigest()==row['graph_sha256'];keys.add(key)
assert len(keys)==len(manifest['representatives'])==84
receipt=json.loads((R/'marker_family/novelty.json').read_text())
assert m.sha(C/'manifest.json')==receipt['frozen_corpus_manifest_sha256']
for row in receipt['results']:
 p=R/'marker_family'/row['name']/'machine.native.tm';assert m.sha(p)==row['sha256']
 st,T=m.parse(p);assert m.canonical(T,st)not in keys and m.canonical(T,st,True)not in keys
 assert row['matches']==row['reflected_matches']==[]
print('PASS: four marker tables against84 frozen rooted graphs, including global reflection')
