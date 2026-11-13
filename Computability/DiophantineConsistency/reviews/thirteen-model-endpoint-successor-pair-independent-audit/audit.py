#!/usr/bin/env python3
"""Read-only complete paired successor artifact and statement-inventory audit."""
import collections,hashlib,json,re,subprocess,sys,tarfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/thirteen-model-endpoint-successor';PLAN=BASE/'research/thirteen-model-endpoint-closure';OUT=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01');SNAP=Path('/tmp/ipra-thirteen-endpoint-source-01');HIST=Path('/tmp/ipra-aq29-fresh-project-pair');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');PARENTAUDIT=BASE/'reviews/thirteen-model-endpoint-closure-independent-audit'
RECEIPT='8cf5b948a9442105a88627653e99e78d395a8f40f496b88e9adb6e439630e5cd';PROGRESS='d4cf3098987576422ea21b81b7c90c2151fa1d8cdf969cdc0271524490af12ac';ARCHIVE='f521d817bfa1233a50fdf78e5c9945b5f890dac71dc9e5f8eb6bcb43f7ea34f9';SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
EXTRA=[('DiophantineConsistency.Thirteen69Nodes',BASE/'research/thirteen69-dag-binding/Thirteen69Nodes.lean',['DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ThirteenCarrier']),('DiophantineConsistency.Thirteen69Cuts',BASE/'research/thirteen69-dag-binding/Thirteen69Cuts.lean',['DiophantineConsistency.Thirteen69Nodes']),('Model69EndpointBindingDraft',PLAN/'Model69EndpointBindingDraft.lean',['DiophantineConsistency.ModelThirteenCarrier','DiophantineConsistency.Thirteen69Cuts']),('Model69EndpointChecks',PKG/'Model69EndpointChecks.lean',['Model69EndpointBindingDraft'])]
EXPECTED_NAMES=['DiophantineConsistency.ModelThirteenCarrier.complete','DiophantineConsistency.ModelThirteenCarrier.sameNoZero69','DiophantineConsistency.ModelThirteenCarrier.bridge69','DiophantineConsistency.ModelThirteenCarrier.native_equivalence69','DiophantineConsistency.ModelThirteenCarrier.standard_equivalence69','DiophantineConsistency.ModelThirteenCarrier.reference_equivalence69','Model69EndpointBindingDraft.eval_equal','Model69EndpointBindingDraft.shifted_zero_equal']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
    if not b:raise ValueError(m)
def warning_class(msg):
    if msg.startswith('automatically included section variable(s) unused'):return 'unused_section_variable'
    if msg.startswith('Variable name '):return 'unused_variable'
    if msg.startswith('This simp argument is unused:'):return 'unused_simp_argument'
    if msg.startswith("try 'simp' instead of 'simpa'"):return 'simp_suggestion'
    if msg.startswith('`push_neg` has been deprecated'):return 'push_neg_deprecation'
    if msg.startswith('`mul_le_mul_left\'` has been deprecated'):return 'multiplication_deprecation'
    if msg.endswith(' tactic does nothing'):return 'unused_tactic'
    if msg.startswith('this tactic is never executed'):return 'unreachable_tactic'
    if msg.startswith('Used `tac1 <;> tac2`'):return 'sequencing_suggestion'
    if msg.startswith('Left-hand side of simp theorem is headed'):return 'simp_index_performance'
    raise ValueError('unclassified warning '+msg)
def guardcheck(guards):
    import os
    for key,val in guards.items():
        p=Path(key)
        if val is None:need(not os.path.lexists(p),'unexpected companion '+key)
        else:need(p.is_file() and str(p.resolve())==val['realpath'] and sha(p)==val['sha256'],'guard drift '+key)
def main():
    names=('RESULT.md','author-axiom-inventory.txt','peer-axiom-inventory.txt','compiler-logs.tar.gz','progress.json','replay-receipt.json','terminal-observation.json')
    for name in names:
        p=PKG/name;b=subprocess.run(['git','show','2ea5025234:'+p.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
        need(hashlib.sha256(b).hexdigest()==sha(p),'committed evidence '+name)
    obs=json.loads((PKG/'terminal-observation.json').read_bytes());need(obs['session']==90536 and obs['actual_exit_code']==0 and obs['launch_head']=='ca3a38b5691987096e020a795f8bda6d423f2c5c' and obs['receipt_sha256']==RECEIPT and obs['progress_sha256']==PROGRESS and obs['compiler_logs_archive_sha256']==ARCHIVE and obs['stdout_final']=='PASS_PAIRED_THIRTEEN_ENDPOINT_SUCCESSOR '+RECEIPT,'outer observation')
    need(sha(PKG/'replay-receipt.json')==sha(OUT/'receipt.json')==RECEIPT and sha(PKG/'progress.json')==sha(OUT/'progress.json')==PROGRESS and sha(PKG/'compiler-logs.tar.gz')==ARCHIVE,'evidence hashes')
    r=json.loads((PKG/'replay-receipt.json').read_bytes());need(r['status']=='PASS_PAIRED_THIRTEEN_ENDPOINT_SUCCESSOR' and len(r['runs'])==684 and json.loads((PKG/'progress.json').read_bytes())==r['runs'],'receipt rows')
    for path,h in r['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed input '+path)
    need(sha(PKG/'replay.py')==r['driver_sha256']=='a97d57a3290d85025699136b8d547a12c0cb9e90aba482595d0da6fac82e6428','driver hash')
    plan=json.loads((PLAN/'frontier-plan.json').read_bytes());snap=json.loads((SNAP/'manifest.json').read_bytes());need(snap['order']==plan['rebuild_order'] and len(snap['order'])==338 and len(plan['reusable_seeds'])==807,'source frontier')
    parent=json.loads((PARENTAUDIT/'CHECK.json').read_bytes());need(r['audit']==parent and sha(PARENTAUDIT/'CHECK.json')=='ab2255186de1e61028731a47a1c92e89792835efe7317e4560b86861bc002af7','parent receipt')
    guardcheck(r['direct_guards'])
    for side in ('author','peer'):guardcheck(plan['direct_and_seed_output_guards'][side])
    for row in plan['rebuild_external_guards'].values():guardcheck(row['companions'])
    results=[];archive_names=set()
    with tarfile.open(PKG/'compiler-logs.tar.gz','r:gz') as archive:
        members=archive.getmembers();need(len(members)==684 and all(x.isfile() for x in members) and len({x.name for x in members})==684,'archive membership')
        archive_names={x.name for x in members}
        for si,side in enumerate(('author','peer')):
            lib=OUT/side/'lib';state=json.loads((HIST/side/'state.json').read_bytes());seeds=set(plan['reusable_seeds']);available=set(seeds);warnings=collections.Counter();warning_modules=set();reports=[];expectedlogs=set()
            for n in seeds:
                obj=HIST/side/'lib'/Path(*n.split('.')).with_suffix('.olean');outputs=state['outputs'][n]
                need(set(outputs)=={str(obj)[:-6]+s for s in SUFFIXES},'seed output coverage '+n)
                for key,val in outputs.items():
                    need(plan['direct_and_seed_output_guards'][side].get(key,'MISSING')==val,'seed guard binding '+key)
                    dest=lib/Path(key).relative_to(HIST/side/'lib')
                    if val is None:need(not dest.exists() and not dest.is_symlink(),'unexpected seed output '+str(dest))
                    else:need(dest.is_symlink() and dest.resolve()==Path(key).resolve() and sha(dest)==val['sha256'],'seed output '+str(dest))
            work=[(n,SNAP/row['snapshot_path'],row['imports'],row['sha256']) for n in snap['order'] for row in [snap['sources'][n]]]
            work.extend((n,path,deps,r['fixed_inputs_sha256'][str(path)]) for n,path,deps in EXTRA)
            need(len(work)==342,'work count')
            for i,(name,source,imports,sourcehash) in enumerate(work):
                row=r['runs'][342*si+i];obj=lib/Path(*name.split('.')).with_suffix('.olean');log=OUT/side/(name.replace('.','_')+'.log')
                need(row['side']==side and row['module']==name and row['exit']==row['deps_exit']==0 and row['stop_reason'] is None,'child exits/order '+name)
                cmd=row['command'];actualsrc=Path(cmd[-3]);srcr=SNAP/'src' if i<338 else OUT/side/'extra-src'
                expectedsource=source if i<338 else srcr/Path(*name.split('.')).with_suffix('.lean')
                need(cmd[1:4]==['-M4000','-j1','-DElab.async=false'] and cmd[4]=='--root='+str(srcr) and actualsrc==expectedsource and cmd[-2:] == ['-o',str(obj)],'command '+name)
                need(sha(source)==sha(actualsrc)==row['source_sha256']==sourcehash and obj.is_file() and not obj.is_symlink() and sha(obj)==row['object_sha256'],'source/object '+name)
                need(Path(row['log'])==log and sha(log)==row['log_sha256'],'log '+name)
                member=side+'/'+log.name;expectedlogs.add(member);arc=archive.extractfile(member);need(arc is not None and hashlib.sha256(arc.read()).hexdigest()==row['log_sha256'],'archive log '+member)
                deps={str(PACKAGE/'Init.olean')}
                for dep in imports:
                    if dep in available:deps.add(str(lib/Path(*dep.split('.')).with_suffix('.olean')))
                    else:
                        need(dep in plan['rebuild_external_guards'],'unavailable import '+name+' '+dep);deps.add(plan['rebuild_external_guards'][dep]['path'])
                need(set(row['deps_stdout'].splitlines())==deps and all(Path(d).is_file() for d in deps),'direct imports '+name)
                text=log.read_text();need(not re.search(r'(?m)^.*error:|\bsorryAx\b|\bsorry\b',text),'error/admission '+name)
                parsed=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M);need([list(x) for x in parsed]==row['axiom_reports'],'axiom reports '+name)
                for declaration,axioms in parsed:need(set(x.strip() for x in axioms.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},'unexpected axiom '+declaration)
                for line in text.splitlines():
                    if 'warning:' in line:warnings[warning_class(line.split('warning:',1)[1].strip())]+=1;warning_modules.add(name)
                if parsed:reports.append(name)
                if name=='Model69EndpointChecks':
                    need([x[0] for x in parsed]==EXPECTED_NAMES,'exact endpoint names')
                    sets=[set(y.strip() for y in x[1].split(',') if y.strip()) for x in parsed]
                    need(sets==[{'propext','Classical.choice','Quot.sound'}]*6+[{'propext','Quot.sound'},{'propext','Classical.choice','Quot.sound'}],'endpoint axiom sets')
                    need((PKG/(side+'-axiom-inventory.txt')).read_bytes()==log.read_bytes(),'axiom log copy')
                available.add(name)
            need(len(available)==1149 and {p.relative_to(lib) for p in lib.rglob('*.olean')}=={Path(*n.split('.')).with_suffix('.olean') for n in available},'project object inventory '+side)
            need(sum(warnings.values())==128 and len(warning_modules)==33,'warning count '+side)
            results.append({'side':side,'rows':342,'seed_modules':807,'objects':len(available),'warnings':dict(sorted(warnings.items())),'warning_modules':len(warning_modules),'axiom_report_modules':reports})
    need(len(archive_names)==684 and archive_names=={side+'/'+(x['module'].replace('.','_')+'.log') for side in ('author','peer') for x in r['runs'] if x['side']==side},'archive exact files')
    for i in range(342):
        a,b=r['runs'][i],r['runs'][i+342];need(a['module']==b['module'] and all(a[k]==b[k] for k in ('source_sha256','object_sha256','log_sha256')),'sibling equality')
    need(results[0]['warnings']==results[1]['warnings'],'warning class mismatch')
    p=subprocess.run([sys.executable,'-I','-S','-B',str(PARENTAUDIT/'audit.py')],capture_output=True,timeout=300)
    need(p.returncode==0 and not p.stderr and json.loads(p.stdout)==parent,'plan audit rerun')
    print(json.dumps({'status':'PASS_INDEPENDENT_THIRTEEN_ENDPOINT_SUCCESSOR_PAIR_AUDIT','evidence_commit':'2ea5025234','author_receipt_sha256':RECEIPT,'recorded_outer_session':90536,'recorded_outer_exit':0,'launch_head':obs['launch_head'],'parent_audit_rerun_exit':p.returncode,'direct_guard_paths':len(r['direct_guards']),'archive_logs':len(archive_names),'endpoint_axiom_names':EXPECTED_NAMES,'runs':results,'scope':'Artifact audit of paired 338+4 source-current successor and model-level semantic binding. Endpoint iPRA theorem is for positiveShift(expressionAt69 ports); a separate DAG-specific internal proof-transfer client is not included. No dynamic/package-transitive or Foundation outer-wrapper completion claim.'},indent=2))
if __name__=='__main__':main()
