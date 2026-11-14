#!/usr/bin/env python3
"""Build the attributed design and delivery ledgers from pinned input indexes."""
import csv,json,re
from pathlib import Path
P=Path(__file__).resolve().parent
PIN='32d0d8b7d93a63ad4106c18cdb29b37927acdad2'
DOC='Computability/BusyBeaver/Research/PA/docs/'
hist=list(csv.DictReader((P/'historical_files.tsv').open(),delimiter='\t'))
classes=list(csv.DictReader((P/'historical_machines.tsv').open(),delimiter='\t'))
files={(r['packet'],r['file']):r for r in hist}; byclass={r['class']:r for r in classes}
named=list(csv.DictReader((P/'named_194_prior.csv').open()))

def added(name,feature,source,status='P',duplicate='None in the named design roster.'):
    return {'name':name,'status':status,'feature':feature,'duplicate_relationship':duplicate,'source':source,'graph_hash':''}

named += [
 added('PA194B','Physical decoder factors two reader contexts through a dedicated history selector; unchanged source. Four native rows change; 22 self-loop actions.',DOC+'PA194B_PA194G_research_2026-11-14/machine/pa194B.tm'),
 added('PA194G','Saved generalization is U(c,h), with explicit AX binder c and original incoming cached theorem h. Q emitter, no-push MP, original sum Shift; shorter generalization word.',DOC+'PA194B_PA194G_research_2026-11-14/generalizer/machine.tm'),
 added('PA194TDY','Physical cycle of T/D/Y register positions and four router edits; primary source unchanged.',DOC+'pa194_tdy_2026-11-14/artifacts/pa194_tdy.tm'),
 added('PA194P5','Five physical register positions and seven router targets change; primary source unchanged.',DOC+'pa194p5_research_2026-11-14/machine/pa194p5.tm'),
 added('PA194AX11Q6','Eleven-entry/four-operand AX; coefficient-six arithmetic; Q premise exchange; no-push MP; original sum Shift.',DOC+'pa194ax11q6_2026-11-14/candidate/machine/machine.tm'),
 added('PA194AX11QH5','Eleven-entry/four-operand AX; coefficient-five arithmetic; Q premise exchange; no-push MP; cache-only Shift. Final compiled contradiction detection uses Pop.',DOC+'pa194_ax11qh5_2026-11-14/machine/machine.tm',duplicate='Repeated byte-for-byte as AX11QH5 in current incoming pa194_research_2026-11-14.zip.'),
 added('PA194AX11H','Eleven-entry/four-operand AX plus H cache-only Shift; corrected final Pop compiler and one removed source increment. Original distribution, coefficient four.','docs/incoming/pa194_ax11h_research_2026-11-14.zip!pa194_ax11h_research_2026-11-14/machine/machine.tm',status='R'),
 added('PA194AX11QH','Eleven-entry/four-operand AX plus Q premise exchange, no-push MP and H cache-only Shift; coefficient four.','docs/incoming/pa194_ax11qh_research_2026-11-14.zip!pa194_ax11qh_research_2026-11-14/candidate/machine/machine.tm',status='R'),
 added('PA194AX11S','AX11 with symmetric original-sum comparison, preserving the sum guard (t+h=1) and the four-operand command interface.','docs/incoming/pa194_ax11s_study.zip!pa194_ax11s_study/machine/machine.tm',status='R'),
 added('PA1944L','Reassociate four-increment decoder as ((i,(i,i)),i), add one helper and one contextual fold: 135+67-8=194. Exact primary source unchanged.','docs/incoming/pa1944l_research_2026-11-14.zip!pa1944l_research/machine/machine.tm',status='R'),
 added('PA194HX','Swap physical H/X register blocks; primary source unchanged.','docs/incoming/pa194_research_2026-11-14.zip!pa194_research_2026-11-14/hx194/machine/pa194hx.tm',status='R'),
]
occ={}
CENSUS=next((P/n for n in ['census_full','census_tm','census'] if (P/n/'summary.json').exists()),P/'census')
if (CENSUS/'occurrences.csv').exists():
    occ={r['locator']:r for r in csv.DictReader((CENSUS/'occurrences.csv').open())}

def resolve_locator(source):
    source=source.replace(' @ ','#')
    if source in occ:return occ[source]['class']
    key=None
    if source.startswith('docs/incoming/') and '.zip!' in source:
        before,inner=source.split('!',1);packet=Path(before).stem
        if '/' in inner:
            rest=inner.split('/',1)[1];key=packet,rest
            alt=DOC+packet+'/'+rest
            if alt in occ:return occ[alt]['class']
    elif source.startswith(DOC):
        packet,rest=source[len(DOC):].split('/',1);key=packet,rest
    old=files.get(key)
    if old:
        kept=byclass[old['class']]['kept_file']
        if kept in occ:return occ[kept]['class']
    return None
for r in named:
    source=r['source']; key=None
    if source.startswith(DOC):
        q=source[len(DOC):];packet,rest=q.split('/',1);key=packet,rest
    elif source.startswith('docs/incoming/') and '.zip!' in source:
        before,inner=source.split('!',1);packet=Path(before).stem
        if '/' in inner:key=packet,inner.split('/',1)[1]
    old=files.get(key)
    r['historical_class']=old['class'] if old else ''
    r['current_table_locator']=byclass[old['class']]['kept_file'] if old else source
    r['source_byte_sha256']=old['sha256'] if old else ''
    r['source_start_metadata']=old['start'] if old else '0 (README and dense-table convention)'
    z=occ.get(r['current_table_locator'])
    r['current_canonical_class']=z['class'] if z else ''
    if z:
        r['kept_table_byte_sha256']=z['source_sha256']
        r['kept_start_metadata']=z['start'] or 'unspecified in table'
        r['kept_start_declared_in_comment']=z['declared_start']
    else:
        r['kept_table_byte_sha256']='';r['kept_start_metadata']='';r['kept_start_declared_in_comment']=''
    r['reported_evidence']='relative weak-arithmetic construction; absolute iPRA calibration explicitly open' if r['status']=='R' else 'historical principal construction with written PA calibration claim' if r['status']=='P' else 'supplementary construction; narrower attributed evidence'
    r['proof_status']='No completed literal-machine iPRA/Con(PA) calibration established by this audit.'
    r['pin']=PIN
with (P/'named_designs.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=list(named[0]));w.writeheader();w.writerows(named)
(P/'named_designs.json').write_text(json.dumps(named,indent=2))

ledger=[]
for line in (P/'filed_README.md').read_text().splitlines():
    if not line.startswith('| [`'):continue
    x=[q.strip() for q in line.strip('|').split('|')]
    if len(x)!=9:raise ValueError(x)
    packet=re.search(r'\[`([^`]+)`\]',x[0])[1]
    ledger.append({'packet':packet,'location':DOC+packet,'arrival':x[1],'wrapper':x[2].strip('`'),'attributed_summary':x[3],'placed_members':x[4],'upstream_copies':x[5],'sibling_archives':x[6],'ignored_members':x[7],'duplicate_tables':x[8],'source':'Computability/BusyBeaver/Research/PA/docs/README.md','pin':PIN})
incoming={
 'pa1944l_research_2026-11-14':'4L physical decoder; relative halting transfer, bounded-store argument and countermodels; no absolute iPRA theorem or sub-194 result.',
 'pa194_ax11h_research_2026-11-14':'AX11H composition; relative refutation compiler, literal checks and padding countermodel; absolute iPRA endpoint open.',
 'pa194_ax11qh_research_2026-11-14':'AX11QH composition; relative halting transfer, premise-exchange proof and literal checks; absolute iPRA endpoint open.',
 'pa194_ax11s_study':'AX11S symmetric sum-Shift; relative source equivalence, coefficient-three obstruction; absolute iPRA endpoint open.',
 'pa194_research_2026-11-14':'HX physical register swap and repeated AX11QH5; command-level weak-arithmetic proof and exact Runtime193 allocation obstruction; absolute iPRA endpoint open.',
}
for packet,summary in incoming.items():
    ledger.append({'packet':packet,'location':'docs/incoming/'+packet+'.zip','arrival':'present at pinned 2026-11-14 snapshot','wrapper':'see archive','attributed_summary':summary,'placed_members':'','upstream_copies':'','sibling_archives':'','ignored_members':'','duplicate_tables':'','source':'archive README (retained in incoming_readmes.json)','pin':PIN})
assert len(ledger)==82,len(ledger)
with (P/'packet_ledger.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=list(ledger[0]));w.writeheader();w.writerows(ledger)
(P/'packet_ledger.json').write_text(json.dumps(ledger,indent=2))

def tex(t):
    for a,b in [ ('\\',r'\textbackslash{}'),('&',r'\&'),('%',r'\%'),('$',r'\$'),('#',r'\#'),('_',r'\_'),('{',r'\{'),('}',r'\}') ]:t=t.replace(a,b)
    return t
lines=[r'\begin{longtable}{p{.22\linewidth}p{.06\linewidth}p{.63\linewidth}}',r'\toprule Design & Role & Distinguishing feature\\\midrule\endhead']
for r in named:
    lines.append(tex(r['name'])+' & '+r['status']+' & '+tex(r['feature'])+r'\\')
lines.extend([r'\bottomrule\end{longtable}',r'P denotes an attributed principal PA-calibration manuscript; S a supplementary construction; R a newer relative construction explicitly leaving absolute iPRA calibration open. These labels describe source claims, not a fresh proof of every historical machine.'])
(P/'named_designs.tex').write_text('\n'.join(lines)+'\n')

# Reconcile all historical 194-state graph roles, including auxiliaries,
# with this census's own canonical format, using exact table provenance.
frontier=json.loads((CENSUS/'classes.json').read_text())
prior={};unresolved=[]
if (P/'prior_frontier194.csv').exists():
    for r in csv.DictReader((P/'prior_frontier194.csv').open()):
        locs=[r['source']]+json.loads(r['sources'])
        got={resolve_locator(s) for s in locs}-{None,''}
        if len(got)!=1:unresolved.append({'name':r['name'],'matches':sorted(got)})
        else:prior[got.pop()]=r
bynew={r['current_canonical_class']:r for r in named if r['current_canonical_class']}
out=[]
for h,c in sorted(frontier.items()):
    if c['states']!=194:continue
    rows=[v for v in occ.values() if v['class']==h]
    first=next(v for v in rows if v['normalized_sha256']==c['normalized_table'])
    old=prior.get(h);new=bynew.get(h)
    name=new['name'] if new else old['name'] if old else 'Unattributed auxiliary/diagnostic'
    role=new['reported_evidence'] if new else old['evidence_category'] if old else 'research auxiliary; no accepted consistency theorem inferred'
    feature=new['feature'] if new else old['mechanism'] if old else 'See exact occurrence locators; not promoted to a principal design.'
    out.append({'class':h,'name':name,'role':role,'feature':feature,'representative':'tables/'+h+'.tm','representative_source':first['locator'],'representative_source_sha256':first['source_sha256'],'normalized_table_sha256':c['normalized_table'],'table_start_metadata':first['start'] or 'unspecified','start_declared_in_comment':first['declared_start'],'start_caution':'A conventionally inferred zero is not by itself a certified blank start. Consult the cited design README and label map.','recognized_occurrences':len(rows),'strong_class':c['strong_class'],'immediate_action_bisimulation_states':c.get('immediate_action_bisimulation_states'),'sources':[x['locator'] for x in rows]})
(P/'frontier194.json').write_text(json.dumps(out,indent=2))
with (P/'frontier194.csv').open('w') as f:
    w=csv.DictWriter(f,fieldnames=list(out[0]));w.writeheader();w.writerows(out)
(P/'frontier_role_reconciliation.json').write_text(json.dumps({'historical_frontier_rows':len(prior)+len(unresolved),'resolved':len(prior),'unresolved':unresolved,'current194_classes':len(out)},indent=2))
print('named designs',len(named),'packets',len(ledger),'resolved named graph classes',sum(bool(r['current_canonical_class']) for r in named))
print('historical frontier roles resolved',len(prior),'unresolved',unresolved)
