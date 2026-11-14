#!/usr/bin/env python3
"""Produce the pinned packet ledger and annotated 194-control comparison.

Structural counts come from audit_inventory.py. Historical proof/evidence
status is an attribution to each packet, not a fresh proof revalidation.
"""
from pathlib import Path
from collections import Counter
import csv, hashlib, json, re, argparse

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('repo',type=Path)
ap.add_argument('output',type=Path)
args=ap.parse_args()
ROOT=args.repo.resolve()
BASE=ROOT/'Computability/BusyBeaver/Research/PA/docs'
OUT=args.output.resolve()
OUT.mkdir(parents=True,exist_ok=True)

packets=[]
for line in (BASE/'README.md').read_text().splitlines():
    if not line.startswith('| [`'):continue
    parts=[x.strip() for x in line.strip('|').split('|')]
    name=re.search(r'`([^`]+)`',parts[0])[1]
    p=BASE/name
    readmes=sorted(x for x in p.iterdir() if x.is_file() and x.name.lower().startswith('readme'))
    packets.append(dict(packet=name,arrived=parts[1],archive_wrapper=parts[2].strip('`'),reported_contribution=parts[3],placed_files=int(parts[4]),upstream_copies=int(parts[5]),sibling_archives=int(parts[6]),ignored_files=int(parts[7]),duplicate_machine_files=int(parts[8]),readme_files=[str(x.relative_to(ROOT)) for x in readmes],readme_sha256=[hashlib.sha256(x.read_bytes()).hexdigest() for x in readmes]))

classes=list(csv.DictReader((BASE/'MACHINES.tsv').open(),delimiter='\t'))
old=json.loads((BASE/'pa194qns_research_2026-11-13/comparison/frontier194_guide.json').read_text())
annotations={x['official_class']:x for x in old if x['official_class']!='Not in filed MACHINES.tsv'}
later={
'534ec22d':('PA194NS (sum guard)','supported packet construction','Original sum-testing Shift with symmetric comparison and no-push visible-result MP; distinct from cache-only NS=HS.'),
'a544f543':('PA194SUMS','supported packet construction','Original sum-testing Shift with symmetric comparison, preserving primary PA194 command semantics.'),
'dccb97c0':('PA194HA','supported packet construction','Cached-result MP, original sum Shift, and A/D physical-register placement.'),
'56f98add':('PA194HAZ','supported packet construction','HA plus final AX decrement of a register proved zero by a four-site invariant.'),
'11c65a85':('PA194QN = PA194NQ','supported packet construction','Premise-exchanged Q emitter plus no-push N controller and original sum Shift; two deliveries are byte-identical.'),
'5b95f7a9':('PA194H6','supported packet construction','Coefficient-six formula arithmetic, no-push MP, and cached-only Shift.'),
'74486d03':('PA194DHS','supported packet construction','Gamma(D) emitter, no-push MP and cached-only symmetric Shift; 135 + 69 - 10 controls.'),
'table:0033':('Rejected append-zero tail','rejected','Literal append-one to append-zero transplant fails its blank-start behavior: all 194 starts classified, four halt and 190 enter proven blank rays.'),
'120ba3f8':('PA194QH6','supported packet construction','Q emitter, coefficient-six arithmetic, no-push MP, and cached-only Shift.'),
'cd37d8a0':('PA194Q6','supported packet construction','Q emitter plus coefficient-six arithmetic and original dummy-push MP / sum Shift.'),
'da81e6f6':('PA194QNS','supported packet construction','Q emitter, no-push MP and symmetric original sum Shift; two deliveries are byte-identical.'),
'da96c74a':('PA194QS','supported packet construction','Q emitter, original dummy-push MP and symmetric original sum Shift.'),
'dc771eb9':('PA194Q5','supported packet construction','Q emitter plus coefficient-five arithmetic and original dummy-push MP / sum Shift.'),
'table:0137':('PA194N-AD (auxiliary)','research auxiliary','No-push N plus A/D physical-register placement; originally JSON-only comparison candidate, now retained as a literal table.'),
'table:019c':('Q with original controller (QS parent)','research auxiliary','Q emitter with original dummy-push MP and original sum Shift; retained parent of the QS construction, not a separate principal theorem.'),
}

fresh={x['kept_file']:x for x in json.loads((OUT/'catalog_recheck.json').read_text())}
frontier=[]
for c in classes:
    if c['states']!='194':continue
    a=annotations.get(c['class'])
    if a is None:
        opts=[v for k,v in later.items() if c['class'].startswith(k)]
        assert len(opts)==1,c
        name,status,mechanism=opts[0]
        a=dict(name=name,evidence_category=status,mechanism=mechanism)
    f=fresh[c['kept_file']]
    frontier.append(dict(name=a['name'],class_sha256=c['class'],table_class_sha256=c['table_class'],state_count=f['states'],transition_count=f['rows'],designated_start=f['start'],start_basis='declared' if f['declared_start'] is not None else ('dense-zero convention' if f['start'] is not None else 'separate metadata required'),byte_sha256=f['sha256'],evidence_category=a['evidence_category'],mechanism=a['mechanism'],first_packet=c['first_packet'],kept_file=c['kept_file'],original_packet_occurrences=int(c['packets']),original_table_occurrences=int(c['files']),freshly_recomputed_structure=f['matches'],proof_status='Historical packet attribution; ordinary PA mathematical argument or research status as specified, not a freshly elaborated end-to-end theorem.'))

for name,data in [('packet_ledger',packets),('frontier194',frontier)]:
    (OUT/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    with (OUT/(name+'.csv')).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=data[0].keys());w.writeheader()
        for x in data:w.writerow({k:json.dumps(v) if isinstance(v,list) else v for k,v in x.items()})

stats=dict(packets=len(packets),frontier_classes=len(frontier),evidence_statuses=dict(Counter(x['evidence_category'] for x in frontier)),all_catalog_structures_recomputed=all(x['matches'] for x in fresh.values()))
(OUT/'comparison_summary.json').write_text(json.dumps(stats,indent=2)+'\n')
print(json.dumps(stats,indent=2))
