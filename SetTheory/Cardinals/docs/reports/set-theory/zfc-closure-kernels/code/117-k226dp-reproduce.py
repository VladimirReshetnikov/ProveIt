#!/usr/bin/env python3
"""Rebuild and verify the K230 -> K226 transfer without network access.

Default: exact construction, source bridges, two-simulator initialization,
open-tape fold, guarded delayed-port startup, and all 6656 symbolic cases.
--quick omits only the fresh universal runtime derivation; it audits the
retained complete runtime evidence instead, and labels that distinction.
Rocq is not required and is not silently invoked by this script.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, time

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT)); sys.path.insert(0,str(ROOT/'verification'))
sys.path.insert(0,str(ROOT/'vendor/proveit'))
import build, audit_prog230_bridge, audit_source229, audit_upstream, startup, runtime, verify_state_fold

def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def check_manifest():
    path=ROOT/'MANIFEST.sha256'
    if not path.exists(): return {'status':'NOT_YET_SEALED'}
    count=0
    for line in path.read_text().splitlines():
        h,name=line.split('  ',1)
        p=Path(name)
        build.require(not p.is_absolute() and '..' not in p.parts,'Unsafe manifest path')
        build.require(digest(ROOT/p)==h,'Manifest mismatch: '+name); count+=1
    return {'status':'ALL_SHIPPED_FILE_HASHES_PASS','files':count}

def saved_runtime(n):
    report=ROOT/f'evidence/runtime{n}.json'
    d=json.loads(report.read_text()); p=report.with_name(d['cases_file'])
    build.require(d['status']=='UNIVERSAL_MATHEMATICAL_PASS','Saved report is incomplete')
    build.require(d['table_sha256']==digest(ROOT/f'machines/k{n}_old.tm'),'Saved table differs')
    source_name=f'sites{n}.json' if n<=227 else 'sites229.json'
    build.require(d['source_sha256']==digest(ROOT/'source'/source_name),'Saved source differs')
    build.require(d['engine_sha256']==runtime.ENGINE and d['helper_sha256']==runtime.HELPER,'Saved engine differs')
    build.require(digest(p)==d['cases_sha256'],'Saved case data differs')
    cases=json.loads(p.read_text()); sites=json.loads((ROOT/'source'/source_name).read_text())
    wanted=[(i,pos) for i,s in enumerate(sites) for pos in ((False,True) if s[1]=='CD' else (False,))]
    build.require([(c['site_index'],c['positive']) for c in cases]==wanted,'Saved guarded cases incomplete')
    build.require(len(cases)==6656 and d['cases']==6656 and d['all_rows_used'],'Saved coverage differs')
    build.require(all(len(c['duration'])==13 and c['duration'][0]>0 and min(c['duration'])>=0 for c in cases),'Saved positivity failure')
    build.require(sum(c['symbolic_steps'] for c in cases)==d['symbolic_steps']=={226:1596687,227:1591422,228:1614426}[n],'Saved aggregate differs')
    return {'status':'RETAINED_FULL_RUNTIME_EVIDENCE_AUDITED','cases':len(cases),
            'fresh_symbolic_derivation':False,'scope':'Integrity and coverage of retained evidence; not a fresh universal derivation.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick',action='store_true')
    ap.add_argument('--all-runtime',action='store_true',help='Also re-prove the K228 and K227 companions')
    ap.add_argument('--output-dir',type=Path,default=ROOT/'replay')
    a=ap.parse_args(); out=a.output_dir.resolve(); out.mkdir(parents=True,exist_ok=True)
    build.require(__debug__ and not sys.flags.optimize,'Run without -O or PYTHONOPTIMIZE')
    build.require(out!=ROOT,'Use a separate replay directory')
    begin=time.monotonic(); summary={'status':'IN_PROGRESS','mode':'quick' if a.quick else 'full'}
    def checkpoint(name,result):
        summary[name]=result; build.dump(out/'replay.json',summary)
        print(name, result.get('status','PASS'),flush=True)
    checkpoint('shipped_manifest',check_manifest())
    construct=build.construct(out)
    for relative in construct['artifacts']:
        build.require((out/relative).read_bytes()==(ROOT/relative).read_bytes(),'Shipped machine differs from reconstruction')
    for name in ('sites230.json','sites229.json','sites227.json','sites226.json'):
        build.require((out/'source'/name).read_bytes()==(ROOT/'source'/name).read_bytes(),'Shipped source differs from reconstruction')
    checkpoint('construction',{'status':construct['status'],'working_states':226})
    u=audit_upstream.audit(); build.dump(out/'evidence/upstream_audit.json',u); checkpoint('upstream',u)
    p=audit_prog230_bridge.audit(ROOT/'vendor/k230-rocq',out/'source/sites230.json')
    build.dump(out/'evidence/prog230_bridge.json',p); checkpoint('literal_Rocq_source_bridge',p)
    s=audit_source229.audit(out/'source/sites230.json',out/'source/sites229.json',ROOT/'vendor/k230-rocq/machine/sites230.json')
    build.dump(out/'evidence/source229_equivalence.json',s)
    checkpoint('four_source_rewrites',{'status':s['status'],'replacements':s['exact_pattern_replacements']})
    reassociation=subprocess.run([sys.executable,'-B',str(ROOT/'verification/verify_source_reassociation.py'),
        '--old-source',str(out/'source/sites229.json'),'--new-source',str(out/'source/sites227.json'),
        '--output',str(out/'evidence/source227_independent.json')],text=True,capture_output=True)
    build.require(reassociation.returncode==0,'Independent source reassociation failed: '+reassociation.stderr)
    rr=json.loads((out/'evidence/source227_independent.json').read_text())
    checkpoint('source_reassociation',{k:rr[k] for k in ('status','ordered_instruction_count','guarded_case_count','changed_leaf_paths')})
    reassociation226=subprocess.run([sys.executable,'-B',str(ROOT/'verification/verify_source_reassociation.py'),
        '--old-source',str(out/'source/sites227.json'),'--new-source',str(out/'source/sites226.json'),
        '--output',str(out/'evidence/source226_independent.json')],text=True,capture_output=True)
    build.require(reassociation226.returncode==0,'Independent final source rotation failed: '+reassociation226.stderr)
    rx=json.loads((out/'evidence/source226_independent.json').read_text())
    checkpoint('final_source_rotation',{k:rx[k] for k in ('status','ordered_instruction_count','guarded_case_count','changed_leaf_paths')})
    for name,ticks in [('k230_old.tm',408419),('k229_old.tm',409691),('k228_old.tm',409835),('k227_old.tm',409835),('k226_old.tm',409835)]:
        boot=startup.audit(out/'machines'/name,ticks)
        build.dump(out/'evidence'/('startup_'+name+'.json'),boot)
        checkpoint('startup_'+name,{'status':boot['status'],'steps':ticks,'one_cells':len(boot['one_cells'])})
    old,os=verify_state_fold.table(out/'machines/rotated230_old.tm')
    new,ns=verify_state_fold.table(out/'machines/k229_old.tm')
    fold=verify_state_fold.prove(old,new,os,ns,72,90,0,None,5,65,20000)
    build.require(fold['status']=='PASS_ALL_TAPE_POSITIVE_BLOCK_SIMULATION','Local fold not proved')
    build.dump(out/'evidence/fold229.json',fold)
    checkpoint('all_tape_fold229',{k:fold[k] for k in ('status','proved_old_rows','block_length_histogram','symbolic_configurations')})
    result=subprocess.run([sys.executable,'-B',str(ROOT/'verification/verify_delayed_port.py'),
        '--old',str(out/'machines/k229_old.tm'),'--new',str(out/'machines/k228_old.tm'),
        '--old-steps','409691','--startup-reference',str(out/'evidence/startup_k229_old.tm.json'),
        '--output',str(out/'evidence/delayed228.json')],text=True,capture_output=True)
    (out/'evidence/delayed228.log').write_text(result.stdout+result.stderr)
    build.require(result.returncode==0,'Delayed-port audit failed: '+result.stderr)
    d=json.loads((out/'evidence/delayed228.json').read_text())
    checkpoint('delayed_port',{k:d[k] for k in ('status','commuting_rows','matched_checkpoints','old_steps','new_steps')})
    for n,source_name in [(228,'sites229.json'),(227,'sites227.json'),(226,'sites226.json')]:
        if a.quick or (n!=226 and not a.all_runtime):
            checkpoint('runtime'+str(n),saved_runtime(n))
        else:
            r=runtime.prove(out/f'machines/k{n}_old.tm',out/'source'/source_name,out/f'evidence/runtime{n}.json')
            checkpoint('runtime'+str(n),{k:r[k] for k in ('status','cases','symbolic_steps','minimum_actual_steps','all_rows_used')})
            # Derivations are deterministic; timing and path metadata need not be.
            build.require((out/f'evidence/runtime{n}_cases.json').read_bytes()==(ROOT/f'evidence/runtime{n}_cases.json').read_bytes(),'Recomputed derivations differ from shipped case data')
    summary.update(status='QUICK_REPLAY_PASS' if a.quick else 'FULL_REPLAY_PASS',seconds=time.monotonic()-begin)
    build.dump(out/'replay.json',summary)
    print(json.dumps({'status':summary['status'],'seconds':summary['seconds'],'output_dir':str(out)},indent=2),flush=True)

if __name__=='__main__': main()
