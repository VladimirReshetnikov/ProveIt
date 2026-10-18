#!/usr/bin/env python3
"""Bounded serial exact246 blank-prefix continuation; no dependency builds or version query."""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, time
CFG={'module': 'BusyBeaver.ZFC.BootPrefix246Chunk002', 'source_name': 'BootPrefix246Chunk002.lean', 'source_sha256': '3dd4edaa7371c7a0b162dc21f703c00e2f6767572fea13491f6069638f54e048', 'audit_sha256': '38881aa58684c4cf0f0c5d127b956485e73dc10b77e5e4924802b39a79c07a29', 'data_sha256': 'e7abbab0e05e09ee9981ce24e3b46d0c2f5aeba4c897e7b1f2ca13279e3773bb', 'generator': '/tmp/zfc-prefix246-lean/bootstrap-chunks/generate.py', 'generator_sha256': 'db498f284f15b150d6545fa8118c21e4d74b2c58279679187b3bcdc062ae5211', 'template': '/tmp/zfc-prefix246-lean/bootstrap-chunks/check-template.py', 'template_sha256': '9f01a953bee63e80150b1e5ffd24684d6e4c7c91ea3a4e2c641a042d4995943d', 'parents': [{'path': '/tmp/zfc-prefix246-lean/bootstrap-chunks/group01/run1/verification.json', 'sha256': '9281ca779867a4f2df989f7370cf496d7abc04bea985e91b58a8811dad8db5c8', 'module': 'BusyBeaver.ZFC.BootPrefix246Chunk001'}], 'imports': ['BusyBeaver.ZFC.BootPrefix246Chunk001'], 'probes': ['SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.block82944', 'SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.reached82944', 'SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.block99328', 'SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.reached99328', 'SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.block115712', 'SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.reached115712', 'SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.block132096', 'SetTheory.BusyBeaver.ZFC.BootPrefix246Chunk002.reached132096'], 'callers': 11, 'scope': 'Actual blank-run continuation 66560 to 132096; final410735 and runtime/consistency remain separate'}
HERE=Path(__file__).resolve().parent
REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
TABLE=REPO/'Computability/BusyBeaver/Research/ZFC/candidate-prefix246/zfc_prefix246.tm'
TABLE_SHA='89cda615b3ea9fcac07ad6b08e0351faa34841a56935b6f5846d3920f13bc0fc'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(c,m):
    if not c:raise RuntimeError(m)
def imports(p):return re.findall(r'^import\s+(\S+)\s*$',p.read_text(),re.M)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args()
    W=a.output.resolve();need(not W.is_relative_to(REPO) and (not W.exists() or not any(W.iterdir())),'Use a fresh external output directory.')
    S=HERE/CFG['source_name'];A=HERE/'Audit.lean';D=HERE/'data.json';G=Path(CFG['generator']);T=Path(CFG['template'])
    for p,h in [(S,CFG['source_sha256']),(A,CFG['audit_sha256']),(D,CFG['data_sha256']),(G,CFG['generator_sha256']),(T,CFG['template_sha256']),(TABLE,TABLE_SHA)]:
        need(sha(p)==h,'Pinned source/audit/data/generator/template/table changed: '+str(p))
    st=S.read_text();at=A.read_text()
    need(not re.search(r'\b(sorry|admit|axiom|native_decide)\b',st),'Forbidden proof shortcut.')
    need(not re.search(r'set_option\s+max(Heartbeats|RecDepth)',st+at),'Keep default proof limits.')
    need(imports(S)==CFG['imports'] and imports(A)==[CFG['module']],'Source/audit imports changed.')
    need(re.findall(r'^#print axioms (.+)$',at,re.M)==CFG['probes'] and len(re.findall(r'^example\b',at,re.M))==CFG['callers'],'Audit contract changed.')
    selected={};parent_records=[];compiler=None;tc=None
    for parent in CFG['parents']:
        P=Path(parent['path']);need(sha(P)==parent['sha256'],'Pinned predecessor record changed.')
        r=json.loads(P.read_text());parent_records.append((P,r))
        need(r['status']=='PASS' and r['only_standard_axioms'] and r['all_input_provider_postchecks'] and
             r['all_fresh_objects_unchanged_after_audit'] and r['source_object_recorded_before_audit'],'Incomplete predecessor evidence.')
        need([c['label'] for c in r['commands']]==['source','audit'] and all(c['exit_code']==0 for c in r['commands']),'Predecessor source/audit failed.')
        need(r['before']==r['after'],'Predecessor input records changed.')
        for p,h in r['after'].items():need(sha(Path(p))==h,'Predecessor input/provider is stale: '+p)
        if compiler is None:compiler=r['compiler'];tc=r['toolchain_providers']
        else:need(compiler==r['compiler'] and tc==r['toolchain_providers'],'Mixed compiler/toolchain boundaries.')
        fresh=[f for f in r['fresh_modules'] if f['module']==parent['module']]
        need(len(fresh)==1 and fresh[0]['source_sha256']==r['source']['sha256'],'Wrong predecessor fresh module.')
        need(sha(Path(r['source']['snapshot']))==r['source']['sha256'],'Predecessor source snapshot changed.')
        items=list(r['reused_modules'])+[dict(module=parent['module'],source=r['source']['path'],source_sha256=r['source']['sha256'],object=fresh[0]['path'],object_sha256=fresh[0]['sha256'])]
        for row in items:
            need(sha(Path(row['source']))==row['source_sha256'] and sha(Path(row['object']))==row['object_sha256'],'Predecessor provider changed.')
            if row['module'] in selected:
                old=selected[row['module']]
                need(old['source_sha256']==row['source_sha256'] and old['object_sha256']==row['object_sha256'] and Path(old['object']).resolve()==Path(row['object']).resolve(),'Ambiguous predecessor provider.')
            else:selected[row['module']]=dict(row)
    need(compiler is not None and tc is not None,'No checked predecessor.')
    C=Path(compiler['path']);need(sha(C)==compiler['sha256'],'Compiler changed.')
    need([t['module'] for t in tc]==['Init','Lean.Elab.Tactic.Omega'],'Unexpected toolchain boundary.')
    for t in tc:
        p=Path(t['object']);need(sha(p)==t['object_sha256'],'Toolchain object changed.')
        need(p.resolve()==(C.parent.parent/'lib/lean'/Path(t['module'].replace('.','/')).with_suffix('.olean')).resolve(),'Toolchain provider path changed.')
    visiting=set();closure=set();allowed_toolchain={'Lean.Elab.Tactic.Omega'}
    def visit(module):
        if module in allowed_toolchain:return
        need(module in selected,'Unlisted project import '+module)
        need(module not in visiting,'Cyclic project imports.')
        if module in closure:return
        visiting.add(module)
        for child in imports(Path(selected[module]['source'])):visit(child)
        visiting.remove(module);closure.add(module)
    for m in imports(S):visit(m)
    need(closure==set(selected),'Selected provider set is not the exact import closure.')
    W.mkdir(parents=True,exist_ok=True);cache=W/'cache';actual=[]
    for r in selected.values():
        dest=cache/Path(r['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        dest.symlink_to(Path(r['object']).resolve())
        actual.append(dict(module=r['module'],actual_first=str(dest),resolved=str(dest.resolve()),sha256=sha(dest)))
    snap=W/'sources'/Path(CFG['module'].replace('.','/')).with_suffix('.lean');snap.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(S,snap);aud=W/'Audit.lean';shutil.copyfile(A,aud)
    files=[Path(__file__).resolve(),S,A,D,G,T,TABLE,C]+[p for p,r in parent_records]+[Path(t['object']) for t in tc]+[Path(r[k]) for r in selected.values() for k in ['source','object']]
    files=list(dict.fromkeys(files));before={str(p):sha(p) for p in files}
    record=dict(status='PREPARED_NOT_BUILT' if a.prepare_only else 'RUNNING',scope=CFG['scope'],
      source=dict(path=str(S),sha256=sha(S),snapshot=str(snap)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aud)),
      compiler=compiler,compiler_version_query_performed=False,parent_evidence=CFG['parents'],
      reused_modules=list(selected.values()),actual_first_providers=actual,toolchain_providers=tc,
      exact_project_import_closure=True,LEAN_PATH=str(cache),commands=[],fresh_modules=[],before=before,
      limits=dict(threads=1,memory_mebibytes=4096,shared_wall_seconds=120,proof_limits='Lean defaults'),dependency_build=False,downloads=False)
    def save():(W/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    def post():
        record['after']={str(p):sha(p) for p in files};need(record['before']==record['after'],'Input/provider changed.')
        need(sha(snap)==CFG['source_sha256'] and sha(aud)==CFG['audit_sha256'],'Snapshot changed.')
        for r in actual:need(Path(r['actual_first']).resolve()==Path(r['resolved']) and sha(Path(r['actual_first']))==r['sha256'],'Actual first provider changed.')
        record['all_input_provider_postchecks']=True
    save()
    if a.prepare_only:post();save();print(W/'verification.json');return
    env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1');deadline=time.monotonic()+120
    def run(label,cmd):
        t=time.monotonic();remaining=deadline-t;need(remaining>0,'Shared wall budget exhausted.');log=W/(label+'.log')
        try:r=subprocess.run(cmd,cwd=W,env=env,capture_output=True,text=True,timeout=remaining)
        except subprocess.TimeoutExpired as error:
            dec=lambda x:x.decode(errors='replace') if isinstance(x,bytes) else(x or '')
            output=dec(error.stdout)+dec(error.stderr);log.write_text(output)
            record['commands'].append(dict(label=label,command=cmd,cwd=str(W),exit_code=None,timed_out=True,seconds=time.monotonic()-t,log=str(log),output=output));save();raise
        output=r.stdout+r.stderr;log.write_text(output)
        record['commands'].append(dict(label=label,command=cmd,cwd=str(W),exit_code=r.returncode,seconds=time.monotonic()-t,log=str(log),output=output));save()
        need(r.returncode==0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output,label+' failed.')
        return output
    try:
        obj=cache/Path(CFG['module'].replace('.','/')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        output=run('source',[str(C),'-j1','-M4096','--root='+str(W/'sources'),'-o',str(obj),str(snap)])
        need(obj.is_file() and not obj.is_symlink(),'Fresh source object missing.')
        fresh=dict(module=CFG['module'],path=str(obj),sha256=sha(obj),source_sha256=sha(snap))
        record['fresh_modules']=[fresh];record['source_object_recorded_before_audit']=True;save()
        audit_output=run('audit',[str(C),'-j1','-M4096',str(aud)])
        parsed=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",audit_output,re.S)
        need([n for n,b in parsed]==CFG['probes'],'Missing/reordered audit reports.')
        axioms=[dict(name=n,axioms=[x.strip() for x in b.split(',') if x.strip()]) for n,b in parsed]
        need(all(set(r['axioms'])<={'propext','Quot.sound','Classical.choice'} for r in axioms),'Unexpected axiom.')
        need(sha(obj)==fresh['sha256'],'Fresh object changed during audit.');post()
        record.update(status='PASS',named_axiom_probes=len(CFG['probes']),callers=CFG['callers'],actual_axiom_sets=axioms,
          only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=dict(source=output.count('warning:'),audit=audit_output.count('warning:')))
    except Exception as error:
        record.update(status='FAIL',error=str(error))
        try:post()
        except Exception as e:record['postcheck_error']=str(e)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
