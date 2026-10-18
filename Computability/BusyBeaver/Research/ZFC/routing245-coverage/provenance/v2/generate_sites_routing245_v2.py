#!/usr/bin/env python3
"""Generate exact routed-tree coverage source; never simulate or invoke Lean.

The fixed203-row DAG is expanded and compared leaf-for-leaf with the delivered
logical certificate. Each new cut is a closed kernel decision about the imported
TreeRouting245.tree; every join requires both actual children. Three measured
pilot propositions/objects are imported directly, without aliases or replay.
The successor preserves the entire cap64 frontier and reuses thirteen successful
original batch modules; every remaining cut gets its own fresh module.
"""
from __future__ import annotations
import argparse,hashlib,json,re
from collections import Counter
from pathlib import Path

PROGRAM_SHA='060a95566e6162b845b3ee734b4134aefeeb3e9c079de705c2d094ca9119ef0b'
SITES_SHA='f77a3fb9729382a0b8cd24d480639862b63ecb76bbc205542d1fc7077c025745'
SITE_SHA='d05562d7a17c58a45089903977a074ea36559d39a2c5f854d63af5874c951021'
COVERAGE_SHA='643aa151328a65ba292214df01a933adc46408a468faabf273bf736457393cf4'
PILOT_PLAN_SHA='c861f4b83dd94980edaece32b92c74f5a7e876d3c920ece6a616e7fd8d6cf60b'
OLD_MANIFEST_SHA='acc22343a70173e143ccf7cef76c9c7dfa7632b2526d3ca5735cb7d582062f24'
OLD_BATCH_SHA='46c14a9f5225cfb93abbe7d07afe98239e974710ea1045638f6fbbfcb222e62c'
OLD_GUARD_SHA='1d9e00af15d18ea684c2afe28aa31a62a9f0f52f1d000159d158755e7683f66b'
OLD_GENERATOR_SHA='c428e2878845b0af2fd87c479b7fbb0d7beb4a35b4dab311fecc193175a34fb8'
BASE_IMPORTS=['ProgramRouting245','SiteCoverage','SiteRouting245']
NS='SetTheory.BusyBeaver.ZFC.SitesRouting245'
PILOTS={0:('0',0,10,10,13,5),70:('1110100100101011010101000110111010111001',1684,1717,33,43,11),
        174:('111010010010101101010101111111',4684,4731,47,61,11)}

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def desc(p):return dict(path=str(Path(p).resolve()),sha256=sha(p),bytes=Path(p).stat().st_size)
def need(c,m):
    if not c:raise ValueError(m)
def bits(p):return '['+', '.join('true' if c=='1' else 'false' for c in p)+']'
def goal(p):return ('allSites SiteRouting245.checkSite '+bits(p[::-1])+'\n'
                    '      (descend TreeRouting245.tree '+bits(p)+') = true')
def imports(p):return re.findall(r'^import ([A-Za-z0-9_.]+)$',Path(p).read_text(),re.M)

def routed_tree(repo):
    program=repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProgramRouting245.lean'
    plain=repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/68-route245-certificate-sites_logical.json'
    coverage=repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/SiteCoverage.lean'
    need(sha(program)==PROGRAM_SHA and sha(plain)==SITES_SHA,'Exact routed program/certificate changed.')
    need(sha(coverage)==COVERAGE_SHA,'Generic structural coverage source changed.')
    text=program.read_text()
    pat=re.compile(r'^private def row(\d{3}) : Row := \((\(\.[a-z]+ \d+\)|\.halt), (\(\.[a-z]+ \d+\)|\.halt)\)$',re.M)
    def edge(s):
        v=s.strip('()').removeprefix('.').split();return (v[0],int(v[1])if len(v)>1 else None)
    matches=list(pat.finditer(text));rows={int(m[1]):(edge(m[2]),edge(m[3]))for m in matches}
    need(len(matches)==203 and set(rows)==set(range(203)),'Wrong203-row DAG.')
    need('root := 202' in text and 'nnodes := 203' in text and 'def tree : Tree := t202' in text,'Wrong program/tree root.')
    expanded=[]
    def expand(i,p):
        for b,e in zip('01',rows[i]):
            if e[0]=='node':need(0<=e[1]<i,'Non-topological child.');expand(e[1],p+b)
            else:
                need(e[0] in ('inc','decnz','brk','cont','halt'),'Unknown leaf edge.')
                expanded.append((p+b,e))
    expand(202,'')
    sites=json.loads(plain.read_text());kind={'CI':'inc','CD':'decnz','CB':'brk','CC':'cont','CH':'halt'}
    need(expanded==[(p,(kind[k],a))for p,k,a in sites],'Full6460-leaf data/actual DAG mismatch.')
    leaf={p:(i,e)for i,(p,e)in enumerate(expanded)};need(len(leaf)==6460,'Repeated leaf address.')
    meta={}
    def build(p):
        if p in leaf:
            i,e=leaf[p];m=dict(lo=i,hi=i+1,nodes=0,leaves=1,guards=2 if e[0]=='decnz'else 1,height=0)
        else:
            a,b=build(p+'0'),build(p+'1');need(a['hi']==b['lo'],'Leaf intervals are not adjacent.')
            m=dict(lo=a['lo'],hi=b['hi'],nodes=1+a['nodes']+b['nodes'],leaves=a['leaves']+b['leaves'],
                   guards=a['guards']+b['guards'],height=1+max(a['height'],b['height']))
        meta[p]=m;return m
    need(build('')==dict(lo=0,hi=6460,nodes=6459,leaves=6460,guards=8391,height=51),'Wrong complete tree census.')
    return meta,sites,[desc(p)for p in (program,plain,coverage)]

def checked_pilots(plan_path,records_path):
    """Read existing proof evidence only; imports remain the exact checked modules."""
    need(sha(plan_path)==PILOT_PLAN_SHA,'Frozen subtree pilot manifest changed.')
    plan=json.loads(plan_path.read_text());entries={x['index']:x for x in plan['selected_units']}
    records=json.loads(records_path.read_text());need(set(records)=={str(i)for i in PILOTS},'Require all three measured pilot records.')
    out={}
    for i in sorted(PILOTS):
        unit=entries[i];ref=records[str(i)];p=Path(ref['path']).resolve();need(sha(p)==ref['sha256'],'Pilot record changed.')
        d=json.loads(p.read_text());module=f'BusyBeaver.ZFC.SitesRouting245CutPilot{i:03d}';ns='SetTheory.BusyBeaver.ZFC.'+module.rsplit('.',1)[1]
        need(d['status']=='PASS' and d['prepare_only']is False and d['only_standard_axioms'] and
             d['all_input_provider_postchecks'] and d['all_fresh_objects_unchanged_after_audit'] and
             d['source_object_recorded_before_audit'] and d['before']==d['after'],'Incomplete pilot evidence.')
        need((d['named_axiom_probes'],d['callers'])==(1,2) and d['cut_index']==i and d['site_fuel']==4000 and d['margin']==64,'Wrong pilot scope.')
        need([x['label']for x in d['commands']]==['source','audit'] and all(x['exit_code']==0 and not x.get('timed_out',False)for x in d['commands']),'Failed pilot commands.')
        need(tuple(unit[k]for k in ('path','lo','hi','leaves','guards','height'))==PILOTS[i],'Pilot cut changed.')
        need(d['path_bits']==unit['path'] and d['leaf_interval']==[unit['lo'],unit['hi']] and d['guard_cases']==unit['guards'],'Pilot record/cut mismatch.')
        for q,h in d['before'].items():need(sha(q)==h,'Stale pilot input '+q)
        for role in ('source','audit'):
            q=d[role];need(sha(q['path'])==sha(q['snapshot'])==q['sha256']==unit[role]['sha256'],'Pilot source/audit binding differs.')
        fs=d['fresh_modules'];need(len(fs)==1 and fs[0]['module']==module,'Wrong pilot module.')
        f=fs[0];need(all(f[k]==d['source_pass_object'][k]for k in ('module','path','sha256','source_sha256')),'Pilot pre-audit object differs.')
        actual=d['fresh_first_provider_before_audit'];ap=actual.get('actual_first',actual.get('path'))
        need(Path(ap).resolve()==Path(f['path']).resolve() and actual['module']==module and sha(ap)==f['sha256']==actual['sha256'],'Pilot actual provider differs.')
        st=Path(d['source']['path']).read_text();need('theorem checked :\n    '+goal(unit['path'])+' := by\n  decide +kernel\n'in st,'Pilot proposition differs.')
        need(d['actual_axiom_sets'][0]['name']==ns+'.checked' and set(d['actual_axiom_sets'][0]['axioms'])<={'propext','Quot.sound','Classical.choice'},'Unexpected pilot axiom report.')
        site=next(q for q in d['reused_modules']if q['module']=='BusyBeaver.ZFC.SiteRouting245')
        need(site['source_sha256']==SITE_SHA and sha(site['source'])==SITE_SHA,'Wrong actual Site provider.')
        out[i]=dict(index=i,module=module.rsplit('.',1)[1],full_module=module,theorem=ns+'.checked',record=desc(p),
                    source=desc(d['source']['path']),audit=desc(d['audit']['path']),fresh_object=desc(f['path']),
                    source_sha256=f['source_sha256'],probes=1,callers=2,proof_replay=False,
                    source_seconds=d['commands'][0]['seconds'],audit_seconds=d['commands'][1]['seconds'])
    return out

def checked_old_batches(manifest_path,batch_path):
    """Retain only the exact thirteen complete source+audit passes; never replay them."""
    need(sha(manifest_path)==OLD_MANIFEST_SHA and sha(batch_path)==OLD_BATCH_SHA,'Original plan/run changed.')
    old=json.loads(manifest_path.read_text());batch=json.loads(batch_path.read_text())
    root_review=manifest_path.parent.parent/'root-first13-and-timeout-review.json'
    need(sha(root_review)=='4b18e3573f9c65196399f5c2367d1eee7904137a6f09074de067bebd52d3d53a','Root evidence review changed.')
    review=json.loads(root_review.read_text());need(review['status']=='CHECKED_13_ACTUAL_PASSES_AND_PRESERVED_TIMEOUT' and
         review['batch']['sha256']==OLD_BATCH_SHA and review['plan']['sha256']==OLD_MANIFEST_SHA,'Root review binding differs.')
    need(batch['status']=='FAIL' and batch['prepare_only']is False and batch['failed_unit']==13 and
         batch['manifest']['sha256']==OLD_MANIFEST_SHA and batch['guard']['sha256']==OLD_GUARD_SHA,'Wrong interrupted original run.')
    need(sha(batch['guard']['path'])==OLD_GUARD_SHA and sha(old['generator']['path'])==OLD_GENERATOR_SHA,'Original programs changed.')
    for u in old['units']:
        for role in ('source','audit'):
            need(sha(manifest_path.parent/u[role])==u[role+'_sha256'],'Original full source/audit family changed.')
    failed=batch['failed_record'];need(sha(failed['path'])==failed['sha256'],'Original failed record changed.')
    f=json.loads(Path(failed['path']).read_text());need(f['status']=='FAIL' and f['fresh_modules']==[] and
        len(f['commands'])==1 and f['commands'][0]['label']=='source' and f['commands'][0]['timed_out'] and
        f['commands'][0]['exit_code']!=0,'Original timeout scope differs.')
    need(Path(f['commands'][0]['log']).read_text()==f['commands'][0]['output']=='\nTIMEOUT\n','Original timeout log changed.')
    need([x['unit_index']for x in batch['completed_units']]==list(range(13)),'Wrong original complete successes.')
    out={}
    for row in batch['completed_units']:
        i=row['unit_index'];u=old['units'][i];ref=row['record'];p=Path(ref['path']).resolve()
        need(row['module']==u['module'] and row['status']=='PASS' and sha(p)==ref['sha256'],'Original complete record differs.')
        d=json.loads(p.read_text());need(d['status']=='PASS' and d['prepare_only']is False and
            d['before']==d['after'] and all(d[k]for k in ('only_standard_axioms','all_input_provider_postchecks',
                'all_fresh_objects_unchanged_after_audit','source_object_recorded_before_audit')),'Incomplete original record.')
        need((d['named_axiom_probes'],d['callers'])==(u['probes'],u['callers']),'Original audit census differs.')
        need([c['label']for c in d['commands']]==['source','audit'] and all(c['exit_code']==0 and not c.get('timed_out',False)for c in d['commands']),'Original command failed.')
        for c in d['commands']:need(Path(c['log']).read_text()==c['output'],'Original raw log differs.')
        for p0,h in d['before'].items():need(sha(p0)==h,'Original input changed '+p0)
        for role in ('source','audit'):
            q=d[role];need(sha(q['path'])==sha(q['snapshot'])==q['sha256']==u[role+'_sha256'],'Original source/audit binding differs.')
        fs=d['fresh_modules'];need(len(fs)==1 and fs[0]['module']==u['module'],'Wrong original fresh module.')
        fresh=fs[0];need(all(fresh[k]==d['source_pass_object'][k]for k in ('module','path','sha256','source_sha256')),'Original pre-audit object differs.')
        actual=d['fresh_first_provider_before_audit'];ap=actual.get('actual_first',actual.get('path'))
        need(Path(ap).resolve()==Path(fresh['path']).resolve() and actual['module']==u['module'] and
             sha(ap)==fresh['sha256']==actual['sha256'],'Original actual provider differs.')
        prep=d['preparation'];need(sha(prep['path'])==prep['sha256'],'Original preparation changed.')
        r=dict(module=u['module'].rsplit('.',1)[1],full_module=u['module'],record=desc(p),
               source=desc(d['source']['path']),audit=desc(d['audit']['path']),fresh_object=desc(fresh['path']),
               source_sha256=fresh['source_sha256'],probes=u['probes'],callers=u['callers'],
               probe_names=u['probe_names'],origin='original_production',original_unit_index=i,cuts=u['cuts'],
               proof_replay=False,source_seconds=d['commands'][0]['seconds'],audit_seconds=d['commands'][1]['seconds'])
        for ci in u['cuts']:
            need(ci not in out,'Repeated original cut.')
            c=old['cut_frontier'][ci];need(c['module']==r['module'] and not c['reused'],'Original cut binding differs.')
            expected='theorem block_'+str(ci)+' :\n    '+goal(c['path'])+' := by decide +kernel'
            need(expected in Path(r['source']['path']).read_text(),'Original successful cut proposition differs.')
            out[ci]=dict(r,theorem=NS+'.block_'+str(ci))
    need(set(out)==set(range(1,42)),'Original passes must cover exactly cuts1..41.')
    return out,old,[desc(manifest_path),desc(batch_path),desc(Path(batch['guard']['path'])),desc(Path(old['generator']['path'])),desc(Path(failed['path'])),desc(root_review)]

def header(extra):
    return ''.join('import BusyBeaver.ZFC.'+m+'\n'for m in dict.fromkeys(BASE_IMPORTS+extra))+'''\n/-!
Closed coverage of the exact routed245 instruction tree. Every new cut is a
kernel decision about the imported actual subtree with its complete reverse
prefix; every composition requires both actual children. The three measured
pilot modules and thirteen passed original batches are reused directly. No external coverage premise, native proof
evaluation, or enlarged proof limits. Grouping changes only file boundaries.
Adapted from the maintained permutation252/prefix246 coverage generators,
preserving Mira-Cult, Jeff Ketchersid and Wade's program/simulation attribution.
-/
namespace '''+NS+'\nopen RegisterPath RMBisim SiteCoverage\n\n'
def footer():return '\nend '+NS+'\n'
def audit(module,probes,goals):
    s='import BusyBeaver.ZFC.'+module+'\n\nopen SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC\nopen RegisterPath RMBisim SiteCoverage SitesRouting245\n\n'
    for p in probes:s+='#print axioms '+NS+'.'+p+'\n'
    for p,g in zip(probes,goals):s+='\nexample : '+g+' := '+p+'\n'
    return s

def build_plan(repo,pilot_plan,pilot_records,original_manifest,original_batch,cap=64,joins_per_module=16,cuts_per_module=1,max_batch_guards=64):
    need(cap==64,'Pilot reuse is tied to the exact cap64 frontier.')
    meta,sites,inputs=routed_tree(repo);reused=checked_pilots(pilot_plan,pilot_records)
    for r in reused.values():r.update(origin='pilot',probe_names=['checked'])
    successful,old,old_inputs=checked_old_batches(original_manifest,original_batch)
    need(not(set(reused)&set(successful)),'Pilot/original cut overlap.')
    reused.update(successful)
    cuts=[];joins=[]
    def split(p):
        if meta[p]['guards']<=cap:
            i=len(cuts);cuts.append(dict(index=i,path=p,**meta[p],theorem=NS+f'.block_{i}',reused=False));return ('cut',i)
        left,right=split(p+'0'),split(p+'1')
        i=len(joins);joins.append(dict(index=i,path=p,theorem=NS+f'.join_{i}',left=left,right=right,module=f'SitesRouting245Join{i//joins_per_module:03d}'));return ('join',i)
    root=split('');need(len(cuts)==236 and len(joins)==235,'Wrong exact frontier size.')
    need(sum(c['leaves']for c in cuts)==6460 and sum(c['guards']for c in cuts)==8391,'Incomplete cut coverage.')
    need(all(a['hi']==b['lo']for a,b in zip(cuts,cuts[1:])),'Cut intervals do not partition leaves.')
    for i,r in reused.items():
        c=cuts[i]
        expected=PILOTS[i] if r['origin']=='pilot' else tuple(old['cut_frontier'][i][k]for k in ('path','lo','hi','leaves','guards','height'))
        need(tuple(c[k]for k in ('path','lo','hi','leaves','guards','height'))==expected,'Reused cut no longer matches.')
        c.update(module=r['module'],theorem=r['theorem'],reused=True)
    batches=[];current=[];guard_sum=0
    def flush():
        nonlocal current,guard_sum
        if current:batches.append(current);current=[];guard_sum=0
    for c in cuts:
        if c['reused']:flush();continue
        if current and(len(current)>=cuts_per_module or guard_sum+c['guards']>max_batch_guards):flush()
        current.append(c);guard_sum+=c['guards']
    flush()
    for i,cs in enumerate(batches):
        module=f"SitesRouting245Cut{cs[0]['index']:03d}"
        for c in cs:c['module']=module
    files={};units=[]
    def unit(module,source,probes,goals,metadata,aud=None):
        au=audit(module,probes,goals)if aud is None else aud
        files[module+'.lean']=source.encode();files[module+'.audit.lean']=au.encode()
        units.append(dict(module='BusyBeaver.ZFC.'+module,source=module+'.lean',source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                          audit=module+'.audit.lean',audit_sha256=hashlib.sha256(au.encode()).hexdigest(),probe_names=probes,
                          probes=len(probes),callers=len(goals),imports=re.findall(r'^import (\S+)',source,re.M),**metadata))
    for cs in batches:
        text=header([]);names=[]
        for c in cs:
            n=f"block_{c['index']}";names.append(n)
            text+=f"/-- Cut {c['index']}: {c['leaves']} leaves / {c['guards']} guards. -/\ntheorem {n} :\n    {goal(c['path'])} := by decide +kernel\n\n"
        unit(cs[0]['module'],text+footer(),names,[goal(c['path'])for c in cs],
             dict(kind='closed_cuts',cuts=[c['index']for c in cs],guards=sum(c['guards']for c in cs),leaves=sum(c['leaves']for c in cs)))
    def endpoint(ref):return(cuts if ref[0]=='cut'else joins)[ref[1]]
    for i in range(0,len(joins),joins_per_module):
        js=joins[i:i+joins_per_module];module=js[0]['module'];dependencies=[endpoint(q[k])['module']for q in js for k in ('left','right')]
        text=header([m for m in dependencies if m!=module])
        for q in js:
            p=q['path'];text+=f"theorem join_{q['index']} :\n    {goal(p)} :=\n  allSites_join SiteRouting245.checkSite {bits(p[::-1])}\n    (descend TreeRouting245.tree {bits(p+'0')})\n    (descend TreeRouting245.tree {bits(p+'1')})\n    {endpoint(q['left'])['theorem']} {endpoint(q['right'])['theorem']}\n\n"
        unit(module,text+footer(),[f"join_{q['index']}"for q in js],[goal(q['path'])for q in js],
             dict(kind='binary_composition',join_indices=[q['index']for q in js],join_count=len(js)))
    rt=endpoint(root)
    text=header([rt['module']])+'''/-- All6460 leaves and8391 guards of the actual routed decoder. -/
theorem all_sites : allSites SiteRouting245.checkSite [] TreeRouting245.tree = true :=
  '''+rt['theorem']+'''

theorem actual_walk_checked (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d)) :
    SiteRouting245.checkSite (consume P d) e = true :=
  allSites_walk SiteRouting245.checkSite ProgramRouting245.program TreeRouting245.tree
    TreeRouting245.tree_eq all_sites P e d hw

theorem actual_walk_exists (P : List Bool) :
    ∃ e d, walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d) :=
  allSites_walk_total SiteRouting245.checkSite ProgramRouting245.program TreeRouting245.tree
    TreeRouting245.tree_eq all_sites P
'''+footer()
    finalaudit='''import BusyBeaver.ZFC.SitesRouting245

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.all_sites
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.actual_walk_checked
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.actual_walk_exists

example : allSites SiteRouting245.checkSite [] TreeRouting245.tree = true := all_sites

example (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d)) :
    SiteRouting245.checkSite (consume P d) e = true := actual_walk_checked P e d hw

example (P : List Bool) :
    ∃ e d, walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d) :=
  actual_walk_exists P
'''
    unit('SitesRouting245',text,['all_sites','actual_walk_checked','actual_walk_exists'],['closed root','typed checked walk','typed total walk'],dict(kind='closed_final'),finalaudit)
    need(len(units)==208 and sum(u['probes']for u in units)==430 and sum(u['callers']for u in units)==430,'Wrong generated theorem/audit census.')
    reused_modules=list({r['full_module']:r for r in reused.values()}.values())
    need(len(reused_modules)==16 and sum(r['probes']for r in reused_modules)==44 and sum(r['callers']for r in reused_modules)==47,'Wrong actual reuse census.')
    report=dict(status='GENERATED_SOURCE_ONLY_UNBUILT',generator=desc(Path(__file__)),compiler_or_version_called=False,
                inputs=inputs+[desc(pilot_plan),desc(pilot_records)]+old_inputs,program_source_sha256=PROGRAM_SHA,nodes=6459,leaves=6460,guard_cases=8391,
                decoder_depth=51,max_guards_per_cut=cap,joins_per_module=joins_per_module,max_cuts_per_module=cuts_per_module,max_batch_guards=max_batch_guards,
                chunks=236,joins=235,generated_units=len(units),reused_units=reused_modules,reused_unit_count=16,
                complete_probes=474,complete_callers=477,generated_probes=430,generated_callers=430,
                cut_frontier=cuts,join_plan=joins,units=units,root=root,
                leaf_opcode_counts=dict(Counter(k for _,k,_ in sites)),
                scope='Exact routed-tree closed checks and both-child joins. Direct reuse of three actual successful pilots and thirteen original successful batch modules, covering44 cut propositions. Complete all-sites proof and typed arbitrary-pointer walk clients require every generated unit to pass. No bootstrap or PA endpoint claim.')
    return files,report

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--pilot-plan',type=Path,required=True);p.add_argument('--pilot-records',type=Path,required=True)
    p.add_argument('--original-manifest',type=Path,required=True);p.add_argument('--original-batch',type=Path,required=True)
    p.add_argument('--max-guards',type=int,default=64);p.add_argument('--joins-per-module',type=int,default=16)
    p.add_argument('--cuts-per-module',type=int,default=1);p.add_argument('--max-batch-guards',type=int,default=64);a=p.parse_args()
    need(__debug__ and a.max_guards==64 and a.joins_per_module==16 and a.cuts_per_module==1 and a.max_batch_guards==64,'Invalid grouping.')
    repo=a.repo.resolve();out=a.output.resolve();need(not out.is_relative_to(repo) and(not out.exists()or not any(out.iterdir())),'Use fresh external output.')
    files,report=build_plan(repo,a.pilot_plan.resolve(),a.pilot_records.resolve(),a.original_manifest.resolve(),a.original_batch.resolve(),a.max_guards,a.joins_per_module,a.cuts_per_module,a.max_batch_guards)
    out.mkdir(parents=True,exist_ok=True)
    for name,data in files.items():(out/name).write_bytes(data)
    (out/'generation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k]for k in ('status','generated_units','reused_unit_count','chunks','joins','leaves','guard_cases','complete_probes','complete_callers')},indent=2))
if __name__=='__main__':main()
