#!/usr/bin/env python3
"""Package a complete existing Rotation244 bootstrap; no proof or simulation.
Requires an explicitly pinned final unit manifest. Never creates that manifest,
never executes supplied programs and never writes maintained repository files.
"""
from pathlib import Path
import argparse,hashlib,json,re
ROOT=Path('/tmp/zfc-rotation244-bootstrap')
TABLE_SHA='91ff0ff2dfe9155548d21405615934b46784c5e3cb850bbf056682d02b203790'
COMPILED=('.olean','.ilean','.olean.server','.olean.private','.o','.so','.a','.pyc','.c')
STANDARD={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
    if not x:raise ValueError(m)
def desc(p):return dict(path=str(Path(p).resolve()),sha256=sha(p),bytes=Path(p).stat().st_size)
def load(p):return json.loads(Path(p).read_text())
def dump(p,obj):p.write_text(json.dumps(obj,indent=2)+'\n')
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--units',type=Path,required=True);ap.add_argument('--units-sha',required=True);a=ap.parse_args()
    need(__debug__,'No optimized Python.');repo=a.repo.resolve();out=a.output.resolve();M=a.units.resolve()
    need(not out.exists() and not out.is_relative_to(repo) and not out.is_relative_to(ROOT),'Use new external output outside captured tree.')
    need(sha(M)==a.units_sha,'Changed explicit unit manifest.');manifest=load(M)
    need(manifest['status']=='COMPLETE_ACTUAL_ROTATION244_BOOTSTRAP' and manifest['target_steps']==407931,'Incomplete manifest.')
    rows=manifest['units'];need(len(rows)>=3,'Fast, First and completed continuation chain required.')
    current={}
    def pin(p,h):
        p=Path(p).resolve();need(p.is_file() and sha(p)==h,'Changed current input '+str(p))
        need(str(p)not in current or current[str(p)]==h,'Conflicting path identity.');current[str(p)]=h
    units=[];endpoint=0;totals=[0,0]
    for i,row in enumerate(rows):
        kind='fast'if i==0 else'first'if i==1 else'continuation';index=i-1
        module='BusyBeaver.ZFC.FastTableRotation244'if i==0 else'BusyBeaver.ZFC.BootRotation244First'if i==1 else f'BusyBeaver.ZFC.BootRotation244Chunk{index:03d}'
        need(row['kind']==kind and row['module']==module,'Wrong ordered module list.')
        P=Path(row['record']['path']).resolve();I=Path(row['inventory']['path']).resolve();G=Path(row['guard']['path']).resolve()
        for q in ['record','inventory','guard']:pin(row[q]['path'],row[q]['sha256'])
        need(P.is_relative_to(ROOT) and I.parent==G.parent==P.parent.parent,'Unexpected unit paths.')
        e=load(P);iv=load(I);need(e['status']=='PASS'and e['prepare_only']is False and e['before']==e['after'],'Incomplete actual evidence.')
        need(all(e[k]for k in ['only_standard_axioms','source_object_recorded_before_audit','all_input_provider_postchecks','all_fresh_objects_unchanged_after_audit']),'Missing actual postchecks.')
        for f,h in e['before'].items():pin(f,h)
        need(e['before'].get(str(G))==row['guard']['sha256'],'Selected guard not executed input.')
        for role in ['source','audit']:
            q=e[role];pin(q['path'],q['sha256']);pin(q['snapshot'],q['sha256']);need(iv[role]['sha256']==q['sha256'],'Inventory/source identity differs.')
        need(iv['canonical']['sha256']==TABLE_SHA,'Wrong canonical table.');pin(iv['canonical']['path'],TABLE_SHA)
        f=e['fresh_modules'];need(len(f)==1 and f[0]['module']==module,'Wrong fresh module.');f=f[0]
        need(e['source_pass_object']==dict(f,source_command_index=0) and f['source_sha256']==e['source']['sha256'],'Wrong pre-audit capture.')
        pin(f['path'],f['sha256']);ff=e['fresh_first_provider_before_audit']
        need(ff['module']==module and ff['sha256']==f['sha256'] and Path(ff['path']).resolve()==Path(f['path']).resolve(),'Wrong fresh first provider.')
        for q in e['reused_modules']+e['toolchain_providers']:
            if 'source'in q:pin(q['source'],q['source_sha256'])
            pin(q['object'],q['object_sha256']);old=next(x for x in e['actual_first_providers']if x['module']==q['module'])
            need(Path(old['actual_first']).resolve()==Path(q['object']).resolve() and old['sha256']==q['object_sha256'],'Wrong reused first provider.')
        need([c['label']for c in e['commands']]==['source','audit'],'Wrong command order.')
        for c in e['commands']:
            need(c['exit_code']==0 and not c['timed_out'] and c['interrupted']is None and c['command'][:3]==[e['compiler']['path'],'-j1','-M4096'],'Failed or changed command.')
            raw=P.parent/(c['label']+'.log');need(raw.read_text()==c['output'] and sha(raw)==c['log_sha256'],'Raw output differs.')
        need(e['warnings']==0 and all('warning:'not in c['output']for c in e['commands']),'Selected run has warnings.')
        need(e['shared_timeout_seconds']==120 and e['LEAN_NUM_THREADS']=='1'and e['memory_mebibytes']==4096 and not e['global_option_overrides'],'Execution budget changed.')
        need(not e['dependency_build'] and not e['downloads'] and not e['compiler_version_query_performed'],'Unexpected ancillary execution.')
        names=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['path']).read_text(),re.M)
        raw=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",e['commands'][1]['output'],re.M)
        rr=[dict(name=n,axioms=sorted({x.strip()for x in s.split(',')if x.strip()}))for n,s in raw]
        need(rr==e['axiom_reports'] and [q['name']for q in rr]==names and all(set(q['axioms'])<=STANDARD for q in rr),'Axiom reports differ.')
        callers=len(re.findall(r'^example\b',Path(e['audit']['path']).read_text(),re.M));need((len(names),callers)==(e['named_axiom_probes'],e['callers']),'Actual audit census differs.')
        if i==0:need((len(names),callers)==(2,4),'Wrong fast census.')
        else:
            need(iv['unit_index']==index and iv['module']==module and iv['start']==endpoint and iv['final_target']==407931,'Broken prefix chain.')
            need(iv['parents']==[dict(path=units[-1]['record']['path'],sha256=units[-1]['record']['sha256'],module=units[-1]['module'])],'Wrong exact preceding record.')
            for key in ['data','generator']:pin(iv[key]['path'],iv[key]['sha256'])
            need(iv['probes']==names and iv['callers']==callers,'Generated audit census differs.')
            if i==1:need(iv['segments']==[dict(start=0,end=1024,depth=10)]and(len(names),callers)==(4,7),'Wrong first checkpoint.')
            else:need(1<=len(iv['segments'])<=4,'Wrong continuation block count.')
            for seg in iv['segments']:
                need(seg['start']==endpoint and 0<=seg['depth']<=14 and seg['end']==endpoint+2**seg['depth'],'Noncontiguous block.');endpoint=seg['end']
            need(endpoint==iv['endpoint'] and endpoint<=407931,'Wrong checkpoint endpoint.')
        totals[0]+=len(names);totals[1]+=callers
        prep=None
        if row.get('preparation'):
            q=row['preparation'];pin(q['path'],q['sha256']);pr=load(q['path']);need(pr['status']=='PREPARED_NOT_BUILT'and pr['prepare_only']and pr['commands']==[]and pr['fresh_modules']==[],'Preparation mislabeled.');prep=q
        units.append(dict(module=module,kind=kind,record=desc(P),inventory=desc(I),guard=desc(G),preparation=prep,endpoint=endpoint,source=e['source'],audit=e['audit'],fresh=f,probes=len(names),callers=callers,seconds={c['label']:c['seconds']for c in e['commands']}))
    need(endpoint==407931 and units[-1]['kind']=='continuation','Incomplete final chain.')
    iv=load(units[-1]['inventory']['path']);data=load(iv['data']['path']);z=data['checkpoints']['407931'];frame=data['final_frame']
    regbits=[b for v in [0,0,0,3,0,0,3,0,0]+[1]*167 for b in [0]+[1]*(v+1)];right=[0]*181+[1]+regbits
    need(data['final_whole_frame_metadata_match']is True and z['state']==87 and z['head']==-5 and z['left']==[1]+[0]*frame['left_padding']and z['right']==right+[0]*frame['right_padding']and len(z['ones'])==351,'Final complete frame differs.')
    need(iv['actual_run_theorem']=='reached407931'and any(n.endswith('.bootstrap407931')for n in iv['probes'])and any(n.endswith('.bootstrap_active_through')for n in iv['probes']),'Final API missing.')
    for q in manifest.get('reviews',[]):pin(q['path'],q['sha256'])
    # Text history is lossless and deduplicated. Compiled caches remain provenance only.
    extras={M,Path(__file__).resolve(),Path(__file__).with_name('plan.md')}|{Path(q['path']).resolve()for q in manifest.get('reviews',[])}
    def paths():return sorted({p for p in ROOT.rglob('*')if p.is_file()or p.is_symlink()}|extras,key=str)
    initial=paths();aliases=[];blobs={};excluded=[];captured={}
    for p in initial:
        if p.is_symlink():excluded.append(dict(path=str(p),kind='symlink_not_materialized',target=str(p.resolve()),sha256=sha(p)if p.is_file()else None));continue
        raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();captured[str(p)]=h
        if any(p.name.endswith(s)for s in COMPILED):excluded.append(dict(path=str(p),kind='compiled_not_copied',sha256=h,bytes=len(raw)));continue
        try:text=raw.decode('utf-8')
        except UnicodeDecodeError:excluded.append(dict(path=str(p),kind='non_utf8_not_copied',sha256=h,bytes=len(raw)));continue
        blobs.setdefault(h,dict(bytes=len(raw),utf8=text));aliases.append(dict(path=str(p),sha256=h,bytes=len(raw)))
    for q in aliases:need(blobs[q['sha256']]['utf8'].encode()==Path(q['path']).read_bytes(),'History roundtrip differs.')
    out.mkdir();files=[];Q=repo/'Computability/BusyBeaver/Research/ZFC';L=repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC';family=Q/'rotation244-bootstrap';destinations=set()
    def stage_bytes(raw,dst,original=None):
        need(dst not in destinations,'Duplicate destination.');destinations.add(dst);p=out/'files'/str(len(files))/dst.name;p.parent.mkdir(parents=True);p.write_bytes(raw)
        files.append(dict(source=str(p),destination=str(dst),original=str(original)if original else None,sha256=sha(p),bytes=len(raw)))
    def stage(src,dst):stage_bytes(Path(src).read_bytes(),dst,src)
    for u in units:
        name=u['module'].rsplit('.',1)[1];P=Path(u['record']['path']);U=P.parent.parent
        stage(u['source']['path'],L/(name+'.lean'));stage(u['audit']['path'],family/'audits'/(name+'Audit.lean'))
        stage(P,family/'records'/(name+'-verification.json'));stage(u['inventory']['path'],family/'inventories'/(name+'.json'));stage(u['guard']['path'],family/'provenance'/(name+'-check.py'))
        stage(U/'boundary.json',family/'provenance'/(name+'-boundary.json'))
        for label in ['source','audit']:stage(P.parent/(label+'.log'),family/'logs'/(name+'-'+label+'.log'))
        if u['preparation']:stage(u['preparation']['path'],family/'records'/(name+'-prepared.json'))
        if u['kind']!='fast':stage(U/'data.json',family/'data'/(name+'.json'))
    stage(units[0]['record']['path'],Q/'results/fast-table-rotation244-verification.json');stage(units[1]['record']['path'],Q/'results/rotation244-bootstrap-first-verification.json');stage(units[-1]['record']['path'],Q/'results/rotation244-bootstrap-verification.json')
    stage(M,family/'completed-units.json');stage(Path(__file__),family/'provenance/build_packet.py');stage(Path(__file__).with_name('plan.md'),family/'provenance/publication-plan.md')
    for q in manifest.get('reviews',[]):stage(q['path'],family/'reviews'/(q['sha256']+'-'+Path(q['path']).name))
    hp=out/'history.json';dump(hp,dict(schema='exact_utf8_history_v1',roots=[str(ROOT)],aliases=aliases,blobs=blobs,excluded=excluded));stage(hp,family/'history.json')
    text='''Exact Rotation244 fast lookup and 407,931-step blank prefix\n\nAll listed units are existing source/audit PASSES under default proof limits, one thread,4,096MiB and a shared120-second budget per unit. The final literal includes the complete tape and its actual exterior-zero padding. The calibrated runtime frame and binary consistency endpoint are separate obligations. Combined243Simulation transfers a proved rotation endpoint to the243-state machine; this bootstrap packet does not itself claim that endpoint or a PA result.\n\nOriginal guards and generators retain historical scratch/provider paths. Normal Lean imports are maintained, but no clean-checkout guard replay or compiled cache is promised. Every captured UTF-8 alias is recoverable as history.blobs[sha256].utf8 encoded as UTF-8. Excluded objects and symlinks are explicitly listed. Historical uncompiled inventory labels and pending variants remain unchanged; actual selected records are separate. The builder invokes no proof, simulation, supplied verifier or version command.\n'''
    stage_bytes(text.encode(),family/'REPLAY.md')
    publication=dict(status='PASS_EXISTING_ROTATION244_BOOTSTRAP_PUBLICATION',units=units,total_modules=len(units),total_probes=totals[0],total_callers=totals[1],target_steps=endpoint,final_frame=frame,history=dict(sha256=sha(hp),aliases=len(aliases),blobs=len(blobs),excluded=len(excluded)),reviews=manifest.get('reviews',[]),unit_manifest=desc(M),builder=desc(Path(__file__)),proof_execution=False,simulation_execution=False,compiled_objects_published=False,maintained_writes=False)
    pp=out/'publication.json';dump(pp,publication);stage(pp,Q/'results/rotation244-bootstrap-publication.json')
    need(initial==paths(),'Captured tree changed during packaging.')
    for p,h in captured.items():need(sha(p)==h,'Captured input changed '+p)
    for p,h in current.items():need(sha(p)==h,'Selected current input changed '+p)
    for q in files:need(sha(q['source'])==q['sha256'],'Staged bytes changed.')
    dump(out/'map.json',dict(files=files,history=desc(hp),publication=desc(pp),proof_execution=False,maintained_writes=False))
    print(json.dumps(dict(map=desc(out/'map.json'),files=len(files),modules=len(units),probes=totals[0],callers=totals[1]),indent=2))
if __name__=='__main__':main()
