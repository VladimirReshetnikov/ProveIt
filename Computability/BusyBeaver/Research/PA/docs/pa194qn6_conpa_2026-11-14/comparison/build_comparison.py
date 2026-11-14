#!/usr/bin/env python3
"""Build a source-attributed semantic ledger over the pinned literal census."""
from pathlib import Path
import argparse,collections,csv,hashlib,io,json,re,subprocess,zipfile

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('repo',type=Path)
parser.add_argument('--census',type=Path,default=Path(__file__).parent)
args=parser.parse_args()
BASE=args.census
REPO=args.repo
REV='2337ce611a26e308697ccbddb2a1636f989f01c3'
DOCS='Computability/BusyBeaver/Research/PA/docs'
blob_cache={}
def git_bytes(path):
    if path not in blob_cache:
        blob_cache[path]=subprocess.check_output(['git','-C',str(REPO),'show',REV+':'+path])
    return blob_cache[path]
historical_csv=BASE/'attributed_frontier194.csv'
if not historical_csv.exists():
    source='docs/incoming/pa_consistency_reduction_study_2026-11-13.zip'
    member='pa_sub194_research_2026-11-13/comparison/frontier194.csv'
    historical_csv.write_bytes(zipfile.ZipFile(io.BytesIO(git_bytes(source))).read(member))
history=list(csv.DictReader(historical_csv.open()))
historical={r['table_class_sha256']:r for r in history}
classes=json.loads((BASE/'table_classes.json').read_text())
occurrences=json.loads((BASE/'table_occurrences.json').read_text())
summary=json.loads((BASE/'summary.json').read_text())
frontier=[]
for row in classes:
    if row['states'] not in (193,194):continue
    key=row['table_class'];old=historical.get(key);p=row['representative']
    if old:
        name=old['name'];category=old['evidence_category'];mechanism=old['mechanism']
        evidence_source='docs/incoming/pa_consistency_reduction_study_2026-11-13.zip!pa_sub194_research_2026-11-13/comparison/frontier194.csv'
    elif row['states']==193:
        if 'runtime193' in p:
            name='Runtime193 (uninitialized)';category='runtime only; blank startup rejected'
            mechanism='Merge native 301 into 88 and patch two return rows. All 4,780 source outcomes pass; no calibrated blank startup. Original start enters a ray; elementary starts have rejection certificates.'
            evidence_source='docs/incoming/pa_sub194_research_2026-11-13.zip!pa_sub194_research_2026-11-13/README.md'
        else:
            name='Coefficient-three193';category='rejected'
            mechanism='Physical refinement passes, but E3(1,0)=I3(0,1)=6 makes the unchanged numerical calculus inconsistent; a primitive refutation of code1 is supplied.'
            evidence_source=DOCS+'/pa194nq_research_2026-11-13/README.md'
    elif 'pa194qh_conpa_2026' in p:
        name='PA194QH';category='supported packet construction'
        mechanism='Q premise-exchanged quantifier head with coefficient4, visible-top no-push MP and cache-only Shift.'
        evidence_source='docs/incoming/pa194qh_conpa_2026-11-13.zip!pa194qh_2026-11-13/README.txt'
    elif '/companions/PA194R_AD/' in p or '/companions/PA194F_AD/' in p:
        name='PA194R-AD' if '/PA194R_AD/' in p else 'PA194F-AD';category='supplementary construction'
        mechanism='A/D physical-register permutation of the source-certified zero-return R or F machine; packet supplies source contracts and complete startup for this composition.'
        evidence_source='docs/incoming/pa_sub194_research_2026-11-13.zip!pa_sub194_research_2026-11-13/research/reduction/README.txt'
    elif '/rotations/' in p:
        name='Rotation '+Path(p).stem;category='research auxiliary'
        mechanism='An auxiliary source-reader reassociation used as a finite physical search input. Not accepted as a new Con(PA) theorem in its packet.'
        evidence_source='docs/incoming/pa_consistency_research_2026-11-14.zip!pa_sub194_comparison_2026-11-14/README.txt'
    elif 'n6_append0.native.tm' in p:
        name='N6 append-zero input';category='research auxiliary'
        mechanism='Single-row append-zero N6 mutation used only as a heuristic control-sharing search input; changed source/startup context coverage is explicitly unestablished.'
        evidence_source='docs/incoming/pa_consistency_reduction_study_2026-11-13.zip!pa_sub194_research_2026-11-13/research/control_sharing/README.txt'
    elif not row['has_graph_spanning_root']:
        name='194-row diagnostic controls';category='diagnostic fixture'
        mechanism='Padded synthetic controls. At most three controls are reachable from one state. Maximal-component grouping is not a full all-component identity claim.'
        evidence_source='docs/incoming/pa_sub194_research.zip!pa_sub194_research/search/encodings/SEARCH_REPORT.md'
    else:
        raise RuntimeError('Unclassified frontier: '+p)
    frontier.append({'name':name,'states':row['states'],'table_class':key,'existing_catalogue_class':row['existing_class'],
        'evidence_category':category,'mechanism':mechanism,'source':p,'evidence_source':evidence_source,
        'graph_spanning_root':row['has_graph_spanning_root'],'max_reachable':row['max_reachable'],
        'occurrences':row['occurrences'],'distinct_byte_forms':row['distinct_bytes'],
        'audit_boundary':'Table bytes, state counts, reachability and graph identities were freshly computed. Historical correctness labels attribute the supplied manuscripts and receipts; their proofs were not all reconstructed.'})

readme=git_bytes(DOCS+'/README.md').decode()
tracked=list(csv.DictReader((BASE/'tracked_files.tsv').open(),delimiter='\t'))
tracked_paths=[Path(r['path']) for r in tracked]
ledger=[]
for line in readme.splitlines():
    if not line.startswith('| [`'):continue
    fields=[x.strip() for x in line.strip('|').split('|')]
    match=re.search(r'\[`([^`]+)`\]',fields[0])
    if not match:continue
    name=match[1];path=DOCS+'/'+name
    readmes=sorted([p for p in tracked_paths if str(p.parent)==path and p.name.startswith('README')],key=lambda p:(p.suffix!='.md',p.name))
    primary=readmes[0] if readmes else None
    ledger.append({'delivery_number':len(ledger)+1,'delivery':name,'location':'filed packet','source':path,
        'arrival_as_recorded':fields[1],'archive_wrapper':fields[2],'reported_contribution':fields[3],
        'readme':str(primary) if primary else None,
        'readme_sha256':hashlib.sha256(git_bytes(str(primary))).hexdigest() if primary else None,
        'comparison_basis':'Package README and the repository filing description; principal mechanisms further resolved in the frontier ledger.',
        'proof_boundary':'Supplied ordinary mathematical/research claims; not all historical proof checks rerun.'})
assert len(ledger)==61,len(ledger)
incoming={
    'pa194qh_conpa_2026-11-13':('pa194qh_2026-11-13','README.txt','PA194QH combines Q emission, no-push visible MP and cache-only Shift at coefficient4; reports an ordinary PA proof and two physical certificate engines. No sub194 construction.'),
    'pa_consistency_reduction_study_2026-11-13':('pa_sub194_research_2026-11-13','README.md','No new accepted machine. Exact rational obstruction to more than seven net savings in a specified fresh-selector/disjoint-reader-fold model of the fixed primary parent; source-only scanner reassociations; factor3 rejection replay.'),
    'pa_consistency_research_2026-11-14':('pa_sub194_comparison_2026-11-14','README.txt','No accepted sub194 result. Every constant equality offset fails in the fixed coefficient3 interface; mixed-radix, split-gate and physical rotation experiments, plus ordinary PA proof audit.'),
    'pa_sub194_research':('pa_sub194_research','README.txt','MP196 detects contradiction at successful MP, clears the offset and preserves the stack; 196 states. Its boundary invariant makes original Shift halt unreachable. No accepted sub194 result.'),
    'pa_sub194_research_2026-11-13':('pa_sub194_research_2026-11-13','README.md','Runtime193 has verified source contracts but rejected tested blank startups. Proves broader admissible source seeds and supplies two supported194 A/D compositions. Does not construct a193 blank-start consistency machine.')}
for name,(wrapper,readme_name,description) in incoming.items():
    path='docs/incoming/'+name+'.zip'
    readme_bytes=zipfile.ZipFile(io.BytesIO(git_bytes(path))).read(wrapper+'/'+readme_name)
    ledger.append({'delivery_number':len(ledger)+1,'delivery':name,'location':'incoming archive','source':path,
        'arrival_as_recorded':'present at pinned revision','archive_wrapper':wrapper,'reported_contribution':description,
        'readme':path+'!'+wrapper+'/'+readme_name,'readme_sha256':hashlib.sha256(readme_bytes).hexdigest(),
        'comparison_basis':'Current archive README and identified proof/search sections.',
        'proof_boundary':'Reports scoped new mathematics, physical checks or research failure; no completed end-to-end Lean/iPRA theorem.'})
assert len(ledger)==66

for name,data in [('frontier_193_194.json',frontier),('packet_ledger.json',ledger)]:
    (BASE/name).write_text(json.dumps(data,indent=2)+'\n')
for name,data in [('frontier_193_194.csv',frontier),('packet_ledger.csv',ledger)]:
    with (BASE/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(data[0]));w.writeheader();w.writerows(data)

full=[x for x in frontier if x['states']==194 and x['graph_spanning_root']]
categories=dict(collections.Counter(x['evidence_category'] for x in full))
summary['delivery_packets']={'filed':61,'incoming':5,'total':66}
summary['frontier194_attributed_evidence_categories']=categories
summary['full_spanning_single_halt_graph_classes']=len({r['table_class'] for r in occurrences if r['has_graph_spanning_root'] and len(r['halting_labels'])==1})
summary['current_root_summaries']={str(n):sum(r['states']==n and r['has_graph_spanning_root'] for r in classes) for n in (193,194,195,196)}
(BASE/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'deliveries':len(ledger),'frontier_rows':len(frontier),'full194':len(full),'categories':categories,'full_spanning_single_halt_graph_classes':summary['full_spanning_single_halt_graph_classes']},indent=2))
