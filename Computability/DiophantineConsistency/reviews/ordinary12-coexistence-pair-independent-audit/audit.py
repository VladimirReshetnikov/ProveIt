#!/usr/bin/env python3
"""Read-only independent artifact audit; does not invoke Lean."""
import collections
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PACKET=BASE/'reviews/ordinary12-coexistence-pair-evidence'
PAIR=Path('/tmp/ipra-ordinary12-coexistence-pair-01')
SNAP=Path('/tmp/ipra-ordinary12-coexistence-source-03')
PROVIDER=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json')
PRE=Path('/tmp/ipra-ordinary12-coexistence-preflight-01.json')
TERM=Path('/tmp/ipra-ordinary12-coexistence-launch-terminal-01.json')
LAUNCH=BASE/'research/ordinary12-ipra-bridge/difference-ring-build-plan/coherent-replay/launch.py'
COMPARE=BASE/'research/fresh-project-closure/compare.py'
EXPECTED_PAIR='a6a5a7ea24d392807c7b98ec989392084f5fdeb88bc5a5c8179f439fbcd6ef33'
EXPECTED_SOURCE='9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded'
EXPECTED_PROVIDER='7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6'
ENDPOINT='DiophantineConsistency.FreeJProviderChecks'
EXPECTED_REPORTS=['DiophantineConsistency.ModelDifferenceRing.internalZero_iff',
                  'FreeJNormZero.ordinary_residual_zero','FreeJNormZero.cleared_auxiliary_pairs']
ALLOWED={'propext','Classical.choice','Quot.sound'}


def need(ok,msg):
    if not ok:raise ValueError(msg)


def digest(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda:f.read(1<<20),b''):h.update(chunk)
    return h.hexdigest()


def load(path):return json.loads(Path(path).read_bytes())


def check_guard(items):
    present=absent=0
    for path,meta in items.items():
        p=Path(path)
        if meta is None:
            need(not os.path.lexists(p),'unexpected companion '+path);absent+=1
        else:
            need(p.is_file() and str(p.resolve())==meta['realpath'] and digest(p)==meta['sha256'], 'changed companion '+path);present+=1
    return {'present':present,'absent':absent}


def warning_class(line):
    msg=line.split('warning:',1)[1].strip()
    if msg.startswith('automatically included section variable(s) unused in theorem '):return 'unused_section_variables'
    if msg.startswith('Variable name ') and msg.endswith(' is not explicitly referenced.'):return 'unused_variable_names'
    if msg=='This simp argument is unused:':return 'unused_simp_argument'
    if msg=='`push_neg` has been deprecated. Prefer using `push Not` instead.':return 'deprecated_tactic'
    raise ValueError('unexpected warning '+msg)


def main():
    packet_rel=PACKET.relative_to(ROOT).as_posix()
    tree=subprocess.run(['git','ls-tree','-r','--name-only','641a64c157','--',packet_rel],cwd=ROOT,capture_output=True,text=True,check=True).stdout.splitlines()
    changed=subprocess.run(['git','diff','--exit-code','641a64c157','--',packet_rel],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    need(len(tree)==154 and changed.returncode==0,'committed evidence packet drift')
    evidence=load(PACKET/'terminal-observation.json'); launch=load(TERM);pre=load(PRE);pair=load(PAIR/'pair-state.json')
    need(evidence['status']=='OBSERVED_LAUNCHER_EXIT' and evidence['observed_exit_code']==0, 'outer observation')
    need(evidence['pair_state_sha256']==EXPECTED_PAIR and digest(PAIR/'pair-state.json')==EXPECTED_PAIR, 'pair state pin')
    need(evidence['preflight_sha256']==digest(PRE)==launch['preflight_sha256'], 'preflight binding')
    need(evidence['launcher_terminal_sha256']==digest(TERM) and launch['outer_exit_code']==0 and launch['stdout']=='MATCHED_PASS 70 rows\n' and not launch['stderr'], 'launcher terminal')
    need(launch['command'][1:4]==['-I','-S','-c'] and launch['command'][5].endswith('/monitor/paired.py') and
         launch['command'][launch['command'].index('--snapshot-sha256')+1]==EXPECTED_SOURCE and
         launch['command'][launch['command'].index('--provider-sha256')+1]==EXPECTED_PROVIDER,'isolated coordinator command')
    need(evidence['observed_stdout']==f"PREFLIGHT_PASS {digest(PRE)}\nPAIR_TERMINAL 0 {digest(TERM)}\nMATCHED_PASS 70 rows\n",'outer stdout')
    for file,live in [('preflight.json',PRE),('launcher-terminal.json',TERM),('pair-state.json',PAIR/'pair-state.json'),
                      ('author-monitor.log',PAIR/'author-monitor.log'),('peer-monitor.log',PAIR/'peer-monitor.log'),('comparator.log',PAIR/'comparator.log')]:
        need((PACKET/file).read_bytes()==live.read_bytes(),'copied packet '+file)
    need(pair['status']=='MATCHED_PASS' and pair['snapshot_sha256']==EXPECTED_SOURCE and pair['provider_sha256']==EXPECTED_PROVIDER,'pair result')
    need(digest(SNAP/'manifest.json')==EXPECTED_SOURCE and digest(PROVIDER)==EXPECTED_PROVIDER,'source/provider hashes')
    manifest=load(SNAP/'manifest.json');names=manifest['order'];sources=manifest['sources']
    need(len(names)==70 and len(set(names))==70 and set(names)==set(sources) and names[-1]==ENDPOINT,'snapshot coverage')
    need(pre['status']=='PASS_PINNED_COEXISTENCE_PREFLIGHT' and pre['source']['project_modules']==70 and pre['provider']['outer_wrapper_exit_observed'] is False,'preflight status')
    for path,h in pre['fixed_sha256'].items():need(digest(path)==h,'fixed script pin '+path)
    for name in names:
        row=sources[name];expected=row['sha256'];a=SNAP/row['snapshot_path'];b=ROOT/row['workspace_path']
        need(digest(a)==digest(b)==expected,'snapshot/workspace source '+name)
    need(digest(ROOT/'lakefile.toml')==manifest['lakefile_sha256'] and digest(ROOT/'lean-toolchain')==manifest['lean_toolchain_sha256'],'source configuration')
    later={}
    for module in ('DiophantineConsistency.ArithmeticOddOrdinateResidue','DiophantineConsistency.ModelThirteenRestoration'):
        path=BASE/'Lean'/Path(*module.split('.')).with_suffix('.lean')
        need(module not in sources and path.is_file(),'later source missing or unexpectedly in closure '+module)
        later[module]=digest(path)
    current_head=subprocess.run(['git','rev-parse','HEAD'],cwd=ROOT,text=True,capture_output=True,check=True).stdout.strip()

    # Recheck the entire declared provider inventory and external guard, not
    # just the handful of imports used directly by the 70 source rows.
    prov=load(PROVIDER);foundation=Path(prov['root'])/'.lake/build/lib/lean/Foundation';overlay=Path(prov['overlay'])
    need(prov['status']=='BUILT' and prov['exit_code']==0 and (overlay/'Foundation').resolve()==foundation.resolve(),'provider receipt')
    guards=check_guard(prov['declared_external_guard'])
    need(len(prov['declared_external_guard'])==14764,'external guard count')
    artifacts=prov['foundation_artifacts'];need(len(artifacts)==1540,'Foundation artifact count')
    for rel,h in artifacts.items():
        q=foundation/rel;need(not Path(rel).is_absolute() and '..' not in Path(rel).parts and not q.is_symlink() and q.is_file() and digest(q)==h,'Foundation artifact '+rel)
    actual={str(p.relative_to(foundation)) for p in foundation.rglob('*') if p.is_file() or p.is_symlink()}
    need(actual==set(artifacts),'Foundation inventory coverage')

    # Independently recheck every pinned review receipt and terminal result.
    spec=importlib.util.spec_from_file_location('launch_audit',LAUNCH);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    for folder,file,rsha,tsha,status,exitkey,shakey in module.REVIEWS:
        r=BASE/'reviews'/folder/file;t=BASE/'reviews'/folder/'terminal-observation.json';a=load(r);b=load(t)
        need(digest(r)==rsha and digest(t)==tsha and a.get('status')==status and b.get(exitkey)==0 and b.get(shakey)==rsha,'review receipt '+folder)
    need(len(module.REVIEWS)==6,'review count')

    normalized=[];warning_counts=[];axiom_counts=[];side_counts=[]
    for entry,label in zip(pair['runs'],('author','peer')):
        need(entry['label']==label and entry['monitor_exit']==entry['builder_exit']==0 and entry['monitor_status']=='EXITED' and entry['builder_status']=='PASS','sibling status '+label)
        for key in ('monitor_log','monitor_terminal','builder_state','builder_log'):
            need(digest(entry[key])==entry[key+'_sha256'],'sibling file '+label+' '+key)
        run=PAIR/label;state=load(run/'child-output/state.json');monitor=load(run/'terminal.json')
        for rel,live in [('terminal.json',run/'terminal.json'),('state.json',run/'child-output/state.json'),('child.log',run/'child.log')]:
            need((PACKET/label/rel).read_bytes()==live.read_bytes(),'copied '+label+' '+rel)
        need(monitor['status']=='EXITED' and monitor['outer_exit_code']==0 and monitor['violation'] is None and monitor['sampled_only'] is True and
             monitor['minimum_free_bytes']>=monitor['reserve_bytes'] and monitor['maximum_logical_bytes']<=monitor['budget_bytes'], 'monitor '+label)
        need(monitor['command'][1:3]==['-I','-S'], 'isolated builder '+label)
        need(monitor['command'][3]==str(BASE/'research/fresh-project-closure/rebuild.py') and
             monitor['command'][monitor['command'].index('--snapshot-sha256')+1]==EXPECTED_SOURCE and
             monitor['command'][monitor['command'].index('--provider-sha256')+1]==EXPECTED_PROVIDER,'builder command '+label)
        need(state['status']=='PASS' and state['phase']=='complete' and state['source_status']=='CURRENT_AT_FINAL_CHECK' and not state['workspace_source_drift'] and
             state['manifest_sha256']==EXPECTED_SOURCE and state['provider_receipt_sha256']==EXPECTED_PROVIDER and len(state['records'])==70 and len(state['outputs'])==70,'builder state '+label)
        need(digest(state['lean_path'])==state['lean_sha256'] and digest(state['foundation_input_path'])==state['foundation_input_sha256'] and digest(BASE/'research/fresh-project-closure/rebuild.py')==state['driver_sha256'],'compiler and driver '+label)
        need(prov['manifest_sha256']==state['foundation_input_sha256'] and load(state['foundation_input_path'])['lean_sha256']==state['lean_sha256'],'provider/compiler binding '+label)
        sideguard=check_guard(state['guarded_companions']);need(len(state['guarded_companions'])==920,'recorded guard count')
        rows=[];warnings=collections.Counter();axioms=collections.Counter();report_count=0;seen=set();expected_objects=set()
        for idx,(name,record) in enumerate(zip(names,state['records'])):
            need(record['module']==name and record['exit']==0 and record['source_sha256']==sources[name]['sha256'],'row '+label+' '+name)
            logfile=Path(record['log']);need(digest(logfile)==record['log_sha256'] and (PACKET/label/'logs'/logfile.name).read_bytes()==logfile.read_bytes(),'copied log '+name)
            text=logfile.read_text();need(not re.search(r'\b(?:sorryAx|sorry|admit|admitted)\b|^.*(?:error:|error\([^)]*\):)',text,re.M),'error/admission '+name)
            for line in text.splitlines():
                if 'warning:' in line:warnings[warning_class(line)]+=1
            reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
            need([v for _,v in reports]==record['axiom_reports'],'report transcript '+name)
            for theorem,vals in reports:
                used={v.strip() for v in vals.split(',') if v.strip()};need(used<=ALLOWED,'unknown axiom '+theorem)
                axioms.update(used);report_count+=1
            if name==ENDPOINT:
                need([n for n,_ in reports]==EXPECTED_REPORTS and all({v.strip() for v in vals.split(',')}==ALLOWED for _,vals in reports),'endpoint reports')
            inputs=record['direct_inputs'];declared=set(sources[name]['imports']);actual_inputs=set(inputs)
            need(declared<=actual_inputs and actual_inputs-declared<={'Init'},'declared direct inputs '+name)
            for dep,meta in inputs.items():
                q=Path(meta['path']);need(q.is_file() and digest(q)==meta['sha256'],'direct input '+dep)
                if dep in sources:
                    need(dep in seen and meta['kind']=='project' and q==(run/'child-output/lib'/Path(*dep.split('.')).with_suffix('.olean')),'fresh project input '+dep)
                else:
                    kind=meta['kind'];need(kind in ('package','toolchain'),'external input type '+dep)
                    extroot=overlay if kind=='package' else Path(state['lean_path']).parent.parent/'lib/lean'
                    need(q==extroot/Path(*dep.split('.')).with_suffix('.olean'),'external input path '+dep)
            olean=run/'child-output/lib'/Path(*name.split('.')).with_suffix('.olean')
            need(not olean.is_symlink() and digest(olean)==record['object_sha256'],'compiled object '+name)
            expected_objects.add(olean);outguard=state['outputs'][name];need(len(outguard)==10 and str(olean) in outguard,'output companion keys')
            check_guard(outguard);need(outguard[str(olean)]['sha256']==record['object_sha256'],'output record')
            rows.append({'module':name,'source':record['source_sha256'],'object':record['object_sha256'],'log':record['log_sha256'],'axiom_reports':record['axiom_reports']});seen.add(name)
        actual_objects={p for p in (run/'child-output/lib').rglob('*') if p.is_file() or p.is_symlink()}
        need(actual_objects==expected_objects,'complete output file inventory '+label)
        need(warnings=={'unused_section_variables':8,'unused_variable_names':2,'unused_simp_argument':1,'deprecated_tactic':1},'warning classification '+label)
        need(report_count==21 and axioms=={'propext':21,'Classical.choice':14,'Quot.sound':16},'axiom report census '+label)
        need(evidence[label+'_state_sha256']==digest(run/'child-output/state.json'),'outer state binding '+label)
        normalized.append(rows);warning_counts.append(dict(warnings));axiom_counts.append(dict(axioms));side_counts.append(sideguard)
    need(normalized[0]==normalized[1],'independent 70-row comparison')
    comparison=load(PAIR/'comparator.log');need(digest(PAIR/'comparator.log')==pair['comparison']['log_sha256'] and pair['comparison']['exit']==0 and
          comparison==pair['comparison']['result'] and comparison['status']=='MATCHED_PASS' and comparison['rows']==70,'recorded comparator')
    env=dict(os.environ)
    for k in list(env):
        if k.startswith('PYTHON') or k in ('LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT'):env.pop(k,None)
    repeat=subprocess.run([sys.executable,'-I','-S','-B',str(COMPARE),str(PAIR/'author/child-output/state.json'),str(PAIR/'peer/child-output/state.json')],cwd=ROOT,env=env,capture_output=True,text=True,timeout=120)
    need(repeat.returncode==0 and json.loads(repeat.stdout)==comparison and not repeat.stderr,'read-only comparator replay')
    rows_digest=hashlib.sha256(json.dumps(normalized[0],sort_keys=True,separators=(',',':')).encode()).hexdigest()
    print(json.dumps({'status':'PASS_INDEPENDENT_70_SOURCE_COEXISTENCE_ARTIFACT_AUDIT',
      'evidence_commit':'641a64c157','pair_state_sha256':EXPECTED_PAIR,'source_manifest_sha256':EXPECTED_SOURCE,'provider_sha256':EXPECTED_PROVIDER,
      'outer_launcher_exit_observed':evidence['observed_exit_code'],'foundation_outer_wrapper_exit_observed':False,
      'sources':len(names),'siblings':2,'compiled_objects':140,'compiler_logs':140,'matched_rows':70,'matched_row_digest':rows_digest,
      'committed_evidence_files':len(tree),
      'workspace_head_at_audit':current_head,'later_sources_outside_pinned_closure':later,
      'provider_artifacts':len(artifacts),'provider_guard':guards,'sibling_guards':side_counts,
      'warnings_per_sibling':warning_counts,'axiom_reports_per_sibling':21,'axiom_occurrences':axiom_counts,
      'endpoint_reports':EXPECTED_REPORTS,'comparator_replay_exit':repeat.returncode,
      'scope':'Read-only post-run artifacts and observations only; no Lean rerun, no complete transitive/dynamic ancestry, no Foundation wrapper exit, no race-free guarantee, no graph transport, calibration, integrality, or iPRA proof.'},indent=2))


if __name__=='__main__':main()
