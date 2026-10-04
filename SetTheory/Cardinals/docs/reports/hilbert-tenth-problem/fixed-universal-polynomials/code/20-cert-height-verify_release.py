#!/usr/bin/env python3
"""Read-only byte verification of a sealed Report46 release."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def need(ok,label):
    if not ok:
        raise RuntimeError(label)

def inventory(root):
    return {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(root.rglob('*')) if p.is_file() and p != root/'MANIFEST.json'}

manifest=json.loads((ROOT/'MANIFEST.json').read_text())
actual=inventory(ROOT)
need(actual==manifest['sha256'],'sealed release file inventory')
packet_pins=json.loads((ROOT/'PACKET_INVENTORY.json').read_text())['sha256']
for path,pin in packet_pins.items():
    need(actual['packets/'+path]==pin,'scientific packet pin '+path)

tex=(ROOT/'Research_Report46.tex').read_text()
free_review=ROOT/'packets/report46-even-rank-manuscript-audit-20261004/REVIEW_PINS.json'
for name,record in json.loads(free_review.read_text())['section_snapshots'].items():
    start=record['start_inclusive'];stop=record['stop_exclusive']
    need(tex.count(start)==1 and tex.count(stop)==1,'unique reviewed section markers '+name)
    excerpt=tex[tex.index(start):tex.index(stop)].encode()
    need(hashlib.sha256(excerpt).hexdigest()==record['sha256'],'manuscript review binding '+name)

for directory, label in [
    ('square-product82-report46-manuscript-audit-20261004','sec:expansion'),
    ('square-product82-report46-allinverse-manuscript-audit-20261004','sec:allinverse'),
]:
    bindings=json.loads((ROOT/'packets'/directory/'SOURCE_BINDINGS.json').read_text())
    marker='\\label{'+label+'}'
    pos=tex.index(marker)
    start=tex.rfind('\\section{',0,pos)
    stop=tex.index('\\section{',pos)
    excerpt=tex[start:stop].encode()
    need(hashlib.sha256(excerpt).hexdigest()==bindings['section_sha256'],
         'analytic manuscript review binding '+label)

print(json.dumps({'status':'PASS','release_files':len(actual),
                  'scientific_packet_files':len(packet_pins),
                  'free83_manuscript_sections_match_audit':True,
                  'both_analytic_manuscript_sections_match_audits':True,
                  'upstream_code_executed':False},indent=2,sort_keys=True))
