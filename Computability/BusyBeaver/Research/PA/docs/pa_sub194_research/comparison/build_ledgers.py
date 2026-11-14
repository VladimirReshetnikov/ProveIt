#!/usr/bin/env python3
"""Add evidence labels to the fresh literal graph census.

Historical labels are attributed to the supplied QN frontier, with new
incoming contributions read from their own reports. They are evidence
classifications, not newly completed proofs of all historical claims.
"""
from pathlib import Path
import csv,hashlib,json,re
from machine_classes import classify

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
CENSUS=HERE/'current_census'
INCOMING=ROOT/'incoming_extracted'
old=INCOMING/'pa194qn_research_2026-11-13/pa194qn_research_2026-11-13/comparison/frontier194.csv'
cache=json.loads((CENSUS/'classification_cache.json').read_text())
annotations={}
for r in csv.DictReader(old.open()):
    k=cache[r['representative_sha256']]['table']
    role=('rejected' if r['status'].startswith('Explicitly rejected') else
          'auxiliary' if r['status'].startswith('Auxiliary') else 'reported construction')
    annotations[k]=dict(name=r['name'],role=role,change=r['change'],
       evidence='Supplied frontier classification; mathematical claims not all freshly reproved here.',
       representative_sha256=r['representative_sha256'])

new=[
('PA194SUMS','PA194NS_research/PA194NS_research/pa194sums.tm','Symmetric destructive comparison preserves original t+h=1 guard and original MP dummy-zero push.'),
('PA194NS (sum guard)','PA194NS_research/PA194NS_research/pa194ns.tm','SUMS controller plus no-push successful MP. Distinct from historical PA194NS=HS, which tests h=1.'),
('PA194DHS','pa194dhs_conpa_2026-11-13/pa194dhs_conpa_2026-11-13/machine/machine.tm','Gamma(D) emitter, no-push MP and symmetric cached-head-only Shift; 135+69-10=194.'),
('PA194H6','pa194h6_conpa_2026-11-13/pa194h6_conpa_2026-11-13/machine/machine.tm','Coefficient-six constructors, no-push MP and cached-head-only Shift; ordinary comparison implementation.'),
('PA194HA','pa194haz_research_2026-11-14/pa194haz_research_2026-11-14/machine/pa194ha.tm','Cached-result MP with original sum Shift and physical A/D register exchange.'),
('PA194HAZ','pa194haz_research_2026-11-14/pa194haz_research_2026-11-14/machine/pa194haz.tm','HA plus final AX return changed to known-zero decrement X.'),
('PA194QN','pa194qn_research_2026-11-13/pa194qn_research_2026-11-13/machine/machine.tm','Quantifier-distribution premise exchange composed with no-push MP and original sum Shift.'),
('Rejected append-zero','pa194dhs_conpa_2026-11-13/pa194dhs_conpa_2026-11-13/search/append_zero/rejected_append0.native.tm','Exact append-zero transplant: four working-state blank starts halt; 190 reach certified blank rays.'),
]
for name,path,change in new:
    data=(INCOMING/path).read_bytes();k=classify(data)['table']
    annotations[k]=dict(name=name,role='rejected' if name.startswith('Rejected') else 'reported construction',
       change=change,evidence='Supplied ordinary mathematical PA argument and executable implementation certificates; no complete Lean/Rocq or iPRA endpoint.' if not name.startswith('Rejected') else 'Explicit rejected-mutation certificate in DHS packet.',representative_sha256=hashlib.sha256(data).hexdigest())
data=json.loads((INCOMING/'PA194NS_research/PA194NS_research/audit/transition_graphs.json').read_text())
r=next(x for x in data['candidates'] if x['name']=='PA194N_AD')
k=classify(r['table'].encode())['table']
annotations[k]=dict(name='PA194N_AD (JSON-only)',role='auxiliary',
   change='A/D physical register exchange applied to no-push PA194N; included only as a graph-comparison candidate.',
   evidence='NS/SUMS report explicitly limits its source/physical proof to its two headline tables.',
   representative_sha256=hashlib.sha256(r['table'].encode()).hexdigest())

rows=[]
for c in json.loads((CENSUS/'classes.json').read_text()):
    if c['states']!=194:continue
    assert c['table_class'] in annotations,c
    rows.append(dict(**annotations[c['table_class']],table_class=c['table_class'],
       states=194,byte_forms=c['byte_forms'],occurrences=c['occurrences'],first_locator=c['locators'][0]))
rows.sort(key=lambda x:(x['role'],x['name']))
with (HERE/'frontier194_annotated.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
(HERE/'frontier194_annotated.json').write_text(json.dumps(rows,indent=2)+'\n')
md=['# Current 194-state frontier','',
 'Snapshot: `2a88cb6a3f823e0de5addf19d725bf8373860c71`. Counts are graph classes, with designated starts ignored only for duplicate detection. Every reported construction retains its own specified blank start.','',
 '| Name | Status | Distinguishing change | Graph prefix |','|---|---|---|---|']
for r in rows:md.append('| '+r['name']+' | '+r['role']+' | '+r['change']+' | `'+r['table_class'][:12]+'` |')
(HERE/'frontier194_annotated.md').write_text('\n'.join(md)+'\n')

ledger=[]
for line in (HERE/'source_delivery_readme.md').read_text().splitlines():
    if not line.startswith('| [`'):continue
    cols=[x.strip() for x in line.strip('|').split('|')]
    name=re.search(r'\[`([^`]+)`\]',cols[0]).group(1)
    ledger.append(dict(packet=name,location='PA/docs',arrival=cols[1],wrapper=cols[2].strip('`'),summary=cols[3]))
extra=[
 ('PA194NS_research','PA194NS_research','SUMS and a sum-guard NS: two194-state symmetric-comparison controllers; N_AD is only an auxiliary explicit JSON table.'),
 ('pa194dhs_conpa_2026-11-13','pa194dhs_conpa_2026-11-13','DHS194 combines Gamma(D), no-push MP and symmetric cache-only Shift. Negative-only diagonal-vacuity proof supplement; rejected append-zero transplant.'),
 ('pa194h6_conpa_2026-11-13','pa194h6_conpa_2026-11-13','H6: radix6, no-push MP, ordinary cached-only comparator;194 states. Explicit symmetric-fold conflict and six-zero scanner failure.'),
 ('pa194haz_research_2026-11-14','pa194haz_research_2026-11-14','HA and HAZ: cached-result MP, A/D physical allocation; HAZ adds final known-zero AX decrement. Both194 states.'),
 ('pa194qn_research_2026-11-13','pa194qn_research_2026-11-13','QN194 combines exchanged quantifier premises and no-push MP with sum guard. Two195-state MP-tail experiments lack complete PA-equivalence proofs.'),
]
for name,wrapper,summary in extra:ledger.append(dict(packet=name,location='docs/incoming',arrival='present at pinned snapshot',wrapper=wrapper,summary=summary))
assert len(ledger)==56,len(ledger)
with (HERE/'packet_ledger56.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(ledger[0]));w.writeheader();w.writerows(ledger)
(HERE/'packet_ledger56.json').write_text(json.dumps(ledger,indent=2)+'\n')
print(json.dumps(dict(frontier_classes=len(rows),role_counts={s:sum(r['role']==s for r in rows) for s in sorted({r['role'] for r in rows})},packet_deliveries=len(ledger)),indent=2))
