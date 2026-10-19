#!/usr/bin/env python3
"""Root-only metadata publication of thirty actual certificate leaves; no compiler or repository writes."""
from pathlib import Path
import argparse,gzip,hashlib,json,os,re
REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
PLAN=Path('/tmp/zfc-w3-control-bisim-split-production-plan')
GENERATION=Path('/tmp/zfc-w3-control-bisim-split-generated1/generation.json')
GENERATION_SHA='b7342f2724acb9c149be7703468b7c3d4a117c12b300fd9447d72b94bc7a3e4c'
BATCH_SHA='a675e8d720015ca69bb0d1d60e935bfc628bd31809271a924a993e49bfdb453a'
GUARD_SHA='e56d862e201df6ced2f37f2d715c7cf08db2bdd078193f9518e7dd20ef701f12'
BOUNDARY_SHA='d9ddf51c348c1d16b4fc4d8c6b073be5c5cfa24455b92ab4e735814ee5997255'
PLANNED_SHA='3499035536525b04f4434238ca307e05a60ce8c9690c3574cacfd397174d91e1'
COMMON_SHA='d6864be086d1b4f4cbaf9ace7637571f54f671fdcf2035404886c1de4bf18723'
PILOT_SHA='bafb7c26397e3e03104ca6c2687106d3762a8dfebdc7559e2229c39c763055bc'
FAIL_SHA='297458b44ed28c0bda68927a3c7406071809dbf6b19314eae2b97364ef0457a7'
PEER=Path('/tmp/zfc-w3-control-bisim-production-peer/review.json')
PEER_SHA='65ded548e0095500dbce4869b8d79a8bb21c09592cf600690039046ae3154481'
PREFIX=Path('Computability/BusyBeaver/Research/ZFC/control-bisim-rotation240-leaves')
LEAN=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC')
RESULT=Path('Computability/BusyBeaver/Research/ZFC/results/control-bisim-rotation240-leaves-publication.json')
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha_bytes(data):return hashlib.sha256(data).hexdigest()
def sha(p):return sha_bytes(Path(p).read_bytes())
def require(condition,message):
    if not condition:raise RuntimeError(message)
def rel(module):return Path(module.replace('.','/')).with_suffix('.olean')
def reports(text):
    matches=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.M)
    return [dict(name=n,axioms=sorted({x.strip()for x in a.split(',')if x.strip()}))for n,a in matches]
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--batch',type=Path,required=True);ap.add_argument('--batch-sha256',required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--extra-history',nargs=2,action='append',default=[],metavar=('PATH','SHA256'))
    a=ap.parse_args();out=a.output.resolve();batchpath=a.batch.resolve()
    require(__debug__,'No optimized Python.');require(not out.exists(),'Fresh packet output required.')
    require(all(not out.is_relative_to(p)for p in [REPO,Path('/home/codex/src/Proofs')]),'Output must be outside maintained repositories.')
    tracked={};payloads={};origins={}
    def pin(path,expected):
        p=Path(path).resolve();key=str(p)
        require(key not in tracked or tracked[key]==expected,'Conflicting input identity '+key)
        if key not in tracked:require(p.is_file()and sha(p)==expected,'Changed input '+key);tracked[key]=expected
        return p
    def load(path,expected):return json.loads(pin(path,expected).read_text())
    def add(destination,data,origin):
        key=str(destination);require(not Path(key).is_absolute()and '..'not in Path(key).parts,'Unsafe destination.')
        require(key not in payloads,'Duplicate destination '+key)
        require(not (REPO/key).exists(),'All leaf packet destinations must be new: '+key)
        payloads[key]=data;origins[key]=origin
    def copy(destination,path,expected=None):
        p=pin(path,expected or sha(path));add(destination,p.read_bytes(),dict(path=str(p),sha256=sha(p)))
    require(a.batch_sha256==BATCH_SHA,'Only the reviewed terminal full batch is accepted.')
    batch=load(batchpath,BATCH_SHA);g=load(GENERATION,GENERATION_SHA)
    boundary=load(PLAN/'boundary.json',BOUNDARY_SHA);planned=load(PLAN/'planned-units.json',PLANNED_SHA)
    pin(PLAN/'check_batch.py',GUARD_SHA);pin(PEER,PEER_SHA);pin(__file__,sha(__file__))
    require(batch['status']=='PASS_SELECTED_LEAF_RANGE'and batch['prepare_only']is False and batch['range']==dict(first=1,last=30),'Terminal full-range PASS required.')
    require(batch['active_unit']is None and batch['before']==batch['after'],'Incomplete/changed batch.')
    require(batch['generation']==dict(path=str(GENERATION),sha256=GENERATION_SHA),'Wrong generation binding.')
    require(g['status']=='GENERATED_SOURCE_ONLY_NO_PROOF_EXECUTION'and g['candidate_execution']is False and not g['fresh_objects'],'Wrong generation provenance.')
    require(g['plan']==dict(path=str(PLAN/'planned-units.json'),sha256=PLANNED_SHA)and g['generator']==boundary['generator'],'Wrong emitter/plan.')
    require([x['index']for x in batch['completed_units']]==list(range(1,31))and len(batch['selected_units'])==30,'Missing/duplicate actual results.')
    require([x['index']for x in g['units']]==list(range(1,31))and len(planned['units'])==30,'Wrong source inventory.')
    for q,h in batch['before'].items():pin(q,h)
    require(batch['before'].get(str(PLAN/'check_batch.py'))==GUARD_SHA,'Wrong executed batch guard.')
    for key,expected,status,census in [('common',COMMON_SHA,'PASS',(2,2)),('pilot',PILOT_SHA,'PASS',(1,1)),('original_failure',FAIL_SHA,'FAIL',None)]:
        d=batch[key];require(d['sha256']==expected,'Wrong preserved ancestor '+key)
        e=load(d['path'],expected);require(e['status']==status,'Changed ancestor status '+key)
        if census:require((e['named_axiom_probes'],e['callers'],e['warnings'])==(*census,0),'Wrong ancestor audit.')
    units=[];source_seconds=0.0;audit_seconds=0.0
    for u,expected,done,selected in zip(g['units'],planned['units'],batch['completed_units'],batch['selected_units']):
        require({k:u[k]for k in expected}==expected,'Changed exact leaf source plan.')
        require(all(done[k]==selected[k]==u[k]for k in ['index','module','start','count','end'])and done['status']=='PASS','Wrong actual leaf interval.')
        i=u['index'];module=f'BusyBeaver.ZFC.ControlBisimRotation240Chunk{i:03d}'
        require(u['module']==module,'Wrong exact module.')
        recordpath=Path(done['record']['path']).resolve()
        require(recordpath==batchpath.parent/f'unit{i:03d}'/'verification.json','Wrong actual result location.')
        e=load(recordpath,done['record']['sha256'])
        require(e['status']=='PASS'and e['prepare_only']is False and(e['named_axiom_probes'],e['callers'],e['warnings'])==(1,1,0),'Non-PASS leaf or warning.')
        require(e['before']==e['after']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit']and e['only_standard_axioms'],'Incomplete leaf postchecks.')
        require(e['certificate_interval']=={k:u[k]for k in ['index','group','start','count','end']}and e['generation']==batch['generation'],'Changed actual source interval.')
        require(e['boundary']==dict(path=str(PLAN/'boundary.json'),sha256=BOUNDARY_SHA)and e['before'].get(str(PLAN/'check_batch.py'))==GUARD_SHA,'Wrong actual guard/boundary.')
        require(e['compiler']==boundary['compiler']and e['reused_modules']==boundary['reused_modules']and e['providers']==boundary['providers']and e['toolchain_providers']==boundary['toolchain_providers'],'Changed actual provider boundary.')
        require(e['provider_evidence']==[batch['common']]and e['exact_project_prerequisite_count']==39,'Wrong immediate actual pedigree.')
        require((e['shared_timeout_seconds'],e['memory_mebibytes'],e['LEAN_NUM_THREADS'],e['global_option_overrides'])==(120,4096,'1',[]),'Changed resource policy.')
        require(e['source_option_overrides']==dict(maxRecDepth=100000,maxHeartbeats=0)and e['audit_option_overrides']==[],'Changed inherited proof limits.')
        require(not e['dependency_build']and not e['downloads']and not e['compiler_version_query_performed'],'Unexpected execution scope.')
        for q,h in e['before'].items():pin(q,h)
        for role in ['source','audit']:
            require(e[role]['path']==u[role]['path']and e[role]['sha256']==u[role]['sha256']==u[role+'_sha256'],'Wrong actual source/audit identity.')
            pin(e[role]['path'],u[role]['sha256']);pin(e[role]['snapshot'],u[role]['sha256'])
        f,=e['fresh_modules'];require(f['module']==module and f['source_sha256']==u['source']['sha256'],'Wrong fresh source object.')
        pin(f['path'],f['sha256'])
        require(e['source_object_recorded_before_audit']and e['source_pass_object']==dict(f,source_command_index=0)and e['fresh_first_provider_before_audit']=={k:f[k]for k in ['module','path','sha256']},'Missing pre-audit object capture.')
        roots=[Path(x)for x in e['LEAN_PATH'].split(os.pathsep)]+[Path(e['compiler']['path']).parent.parent/'lib/lean']
        def first(m):return next((root/rel(m)).resolve()for root in roots if(root/rel(m)).is_file())
        require(first(module)==Path(f['path']).resolve(),'Fresh object is not the first current provider.')
        providers=e['reused_modules']+e['providers']+e['toolchain_providers']
        require(len(e['actual_first_providers'])==len(providers)==44,'Wrong current provider census.')
        actual={x['module']:x for x in e['actual_first_providers']};require(len(actual)==44,'Duplicate provider capture.')
        for q in providers:
            require(first(q['module'])==Path(q['object']).resolve()and actual[q['module']]==dict(module=q['module'],actual_first=str(Path(q['object']).resolve()),sha256=q['object_sha256']),'Changed first-provider identity.')
        require([x['label']for x in e['commands']]==['source','audit'],'Wrong command order.')
        for c in e['commands']:
            expected_cmd=[e['compiler']['path'],'-j1','-M4096','--root='+str(Path(e['audit']['snapshot']).parent)]+(['-o',f['path']]if c['label']=='source'else[])+[e[c['label']]['snapshot']]
            require(c['command']==expected_cmd and c['exit_code']==0 and c['timed_out']is False and c.get('interrupted')is None,'Wrong actual command/result.')
            log=pin(c['log'],c['log_sha256']);require(log.read_text()==c['output'],'Changed raw log.')
            require(not any(x in c['output']for x in ['warning:','error:','sorryAx']),'Unexpected diagnostics.')
            copy(PREFIX/f'unit{i:03d}'/(c['label']+'.log'),log,c['log_sha256'])
        probe='SetTheory.BusyBeaver.ZFC.ControlBisimRotation240Split.check'+format(i,'03d')
        rr=reports(e['commands'][1]['output']);at=Path(e['audit']['snapshot']).read_text()
        require(rr==e['axiom_reports']and [x['name']for x in rr]==[probe]and all(set(x['axioms'])<=STANDARD for x in rr),'Wrong actual axiom report.')
        require(re.findall(r'^#print axioms (\S+)$',at,re.M)==[probe]and len(re.findall(r'^example\b',at,re.M))==1,'Wrong typed audit.')
        copy(LEAN/f'ControlBisimRotation240Chunk{i:03d}.lean',e['source']['path'],e['source']['sha256'])
        copy(PREFIX/f'unit{i:03d}'/'Audit.lean',e['audit']['path'],e['audit']['sha256'])
        copy(PREFIX/f'unit{i:03d}'/'verification.json',recordpath,done['record']['sha256'])
        source_seconds+=e['commands'][0]['seconds'];audit_seconds+=e['commands'][1]['seconds']
        units.append(dict(index=i,module=module,start=u['start'],count=u['count'],end=u['end'],verification=done['record'],source=e['source']['sha256'],audit=e['audit']['sha256'],fresh_object=f['sha256']))
    require(units[0]['start']==128 and units[-1]['end']==3862 and sum(x['count']for x in units)==3734 and all(x['end']==y['start']for x,y in zip(units,units[1:])),'Incomplete exact remaining coverage.')
    for name,path,h in [('generation.json',GENERATION,GENERATION_SHA),('batch.json',batchpath,BATCH_SHA),('check_batch.py',PLAN/'check_batch.py',GUARD_SHA),('boundary.json',PLAN/'boundary.json',BOUNDARY_SHA),('planned-units.json',PLAN/'planned-units.json',PLANNED_SHA),('build_packet.py',Path(__file__),sha(__file__))]:copy(PREFIX/name,path,h)
    # One lossless content-addressed archive; identical text payloads appear once.
    # Text already published directly is referenced by its packet destination.
    direct={sha_bytes(data):key for key,data in payloads.items()};entries=[];blobs={};excluded=[]
    def capture(path,alias):
        p=pin(path,sha(path));data=p.read_bytes();h=sha_bytes(data);text=data.decode('utf-8')
        entries.append(dict(path=alias,original_path=str(p),sha256=h,size=len(data)))
        if h not in direct:blobs.setdefault(h,text)
    history_roots=[('production-plan',PLAN),('generated',GENERATION.parent),('actual-batch',batchpath.parent),('original-memory-failure',Path(batch['original_failure']['path']).parent)]
    for label,root in history_roots:
        for p in sorted(root.rglob('*')):
            if not p.is_file():continue
            relative=p.relative_to(root)
            if 'cache'in relative.parts or p.suffix in {'.olean','.ilean','.olean.server','.pyc'} or '__pycache__'in relative.parts:
                excluded.append(dict(path=label+'/'+str(relative),reason='Compiled/cache payload excluded; actual descriptors retained.'));continue
            capture(p,label+'/'+str(relative))
    capture(PEER,'reviews/production-peer.json')
    peer_source=json.loads(PEER.read_text())['reviewer_source'];capture(pin(peer_source['path'],peer_source['sha256']),'reviews/production-peer-source.py')
    for j,(path,h)in enumerate(a.extra_history):capture(pin(path,h),f'extra-history/{j:03d}/'+Path(path).name)
    require(len({x['path']for x in entries})==len(entries),'Duplicate history path.')
    history=dict(format='content-addressed-utf8-v1',files=entries,blobs=blobs,published_payloads={h:direct[h]for h in {x['sha256']for x in entries}if h in direct},excluded=excluded,scope='Exact bounded plans/generated sources/actual batch and preserved original failure; no dependency cache or unrelated scratch directories.')
    encoded=json.dumps(history,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()
    add(PREFIX/'history.json.gz',gzip.compress(encoded,mtime=0),dict(generated='lossless bounded UTF8 archive'))
    summary=dict(status='ROOT_METADATA_PACKET_FOR_ACTUAL_THIRTY_LEAVES',batch=dict(path=str(batchpath),sha256=BATCH_SHA),generation=dict(path=str(GENERATION),sha256=GENERATION_SHA),units=units,named_axiom_probes=30,callers=30,warnings=0,source_seconds=source_seconds,audit_seconds=audit_seconds,selected_project_prerequisites=39,external_boundaries=3,tools=2,common=batch['common'],pilot=batch['pilot'],original_failure=batch['original_failure'],facade_checked_by_this_packet=False,source_authorship='Leaf generator/guard/facade draft authored by drop_contract; independent production source review by review_upstream_reflection. Root performed all actual executions and alone invokes this publisher.',proof_options=dict(maxRecDepth=100000,maxHeartbeats=0),audit_options='defaults',per_unit_limits=dict(shared_seconds=120,threads=1,memory_mebibytes=4096),whole_dependency_cache_attested=False)
    add(RESULT,(json.dumps(summary,indent=2,ensure_ascii=False)+'\n').encode(),dict(generated='actual leaf publication summary'))
    note=f'''# Remaining packed-control certificate leaves

All thirty remaining intervals passed their individual Lean source and typed audit checks: **30 axiom probes and 30 callers, zero warnings**. They cover entries **128–3,861** of the unchanged 3,862-entry certificate. The separately published first 128-entry pilot completes the finite interval coverage. The final `ControlBisimRotation240` facade has separate actual evidence and publication; this leaf packet makes no final facade, binary consistency or PA theorem claim.

Each source/audit pair had its own shared 120-second deadline, one thread and 4 GiB memory cap. The unchanged concrete-check policy is explicit: source `maxRecDepth 100000`, `maxHeartbeats 0`; audit defaults. Aggregate source/audit times were {source_seconds:.6f}/{audit_seconds:.6f} seconds. Existing Common/provider objects were reused without rebuilding dependencies or replaying their proofs.

The thirty source modules are new canonical files. Every unit retains its exact audit, raw verification record and both raw logs here. `generation.json`, `batch.json`, `check_batch.py`, `boundary.json` and `planned-units.json` retain exact execution provenance. Original scratch paths in those records remain historical; the unchanged guard is not claimed to replay from this publication alone. `history.json.gz` stores bounded UTF-8 history losslessly with content hashes, using references to identical directly published payloads and one copy of every remaining text. Compiled caches are excluded; their exact descriptors remain in actual records.

The original unsplit check failed with a memory exception under the same 4 GiB cap. Its raw failure is preserved in history and at [the original failure checkpoint](../rotation240_pa/control-bisim-first-check/README.md). It was not a timeout and is not promoted to a success. The generator/guard/facade author and independent source reviewer are disclosed in the [publication summary](../results/control-bisim-rotation240-leaves-publication.json). The facade source and original proposed wording preserved in this archive are source history; actual facade evidence is published separately.
'''
    add(PREFIX/'README.md',note.encode(),dict(generated='actual leaf scope note'))
    require(len(payloads)==159 and len([x for x in payloads if x.startswith(str(LEAN)+'/')])==30,'Wrong exact new-file census.')
    for path,h in tracked.items():require(sha(path)==h,'Input changed before packet write '+path)
    out.mkdir()
    mapping=[]
    for key,data in sorted(payloads.items()):
        target=out/key;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
        require(sha(target)==sha_bytes(data),'Written packet mismatch.')
        mapping.append(dict(destination=key,packet_path=str(target),sha256=sha_bytes(data),bytes=len(data),origin=origins[key]))
    for path,h in tracked.items():require(sha(path)==h,'Input changed during packet write '+path)
    record=dict(status='EXTERNAL_PUBLICATION_PACKET_PASS',maintained_files_written=False,compiler_invoked=False,files=mapping,file_count=len(mapping),canonical_new_lean_modules=30,history_text_paths=len(entries),history_unique_embedded_payloads=len(blobs),history_direct_payload_references=len(history['published_payloads']),history_exclusions=len(excluded),before=tracked,after={p:sha(p)for p in tracked},summary_destination=str(RESULT))
    (out/'publication-map.json').write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n');print(out/'publication-map.json')
if __name__=='__main__':main()
