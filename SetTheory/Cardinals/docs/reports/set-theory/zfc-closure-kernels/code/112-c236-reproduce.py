#!/usr/bin/env python3
"""Replay the236-state construction in a fresh, manifest-checked package copy.

Default: rerun finite proofs, exact initialization, formalism checks and the
inherited237 quick suite; audit the supplied complete unbounded receipts.
--full additionally reruns both new unbounded symbolic runtime jobs.
The delivered evidence is never overwritten. Python3.10+; standard library.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile, time, traceback

ROOT=Path(__file__).resolve().parent
PINS={
 'upstream/zfc237/zfc_composed237_old.tm':'a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a',
 'machines/zfc_rotated237_old.tm':'da0b3d1fdd74d56482b9d231119bbbaccdbcadc78e7b7df72c3a734a3a808724',
 'machines/zfc236_old.tm':'ff059535876bc9e1e1e63174ebfd1c10a91c1a818ba0c3f8c4ef2ac51a3cfcc3',
 'machines/zfc236.tm':'d4302309401891d68b93c393e4ad6e24d2abf993dede4a61baa2d3e0c1c53c8e',
 'source/sites_logical.json':'1ebe9691507b2d3236951a31d6b9a7ef548a2cdf90525cd57051992f8ac2626f',
}

def require(c,msg):
    if not c:raise ValueError(msg)
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def write(p,j):
    p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(j,indent=2)+'\n')

def manifest(root):
    m=root/'SHA256SUMS';entries={}
    for line in m.read_text().splitlines():
        if not line:continue
        expected,name=line.split('  ',1);p=Path(name)
        require(len(expected)==64 and all(c in '0123456789abcdef' for c in expected),'Malformed hash')
        require(not p.is_absolute() and '..' not in p.parts and name not in entries,'Unsafe manifest path')
        require((root/p).is_file() and digest(root/p)==expected,'Manifest mismatch: '+name)
        entries[name]=expected
    require(set(PINS)<=set(entries),'Manifest omits pinned artifacts')
    require({'reproduce.py','build_source.py','build_zfc236.py','verification/check_fold236.py','verification/verify_runtime.py'}<=set(entries),'Manifest omits proof programs')
    for p,h in PINS.items():require(entries[p]==h,'Pinned input changed: '+p)
    return entries,{'status':'PASS','files':len(entries),'manifest_sha256':digest(m)}

def table_rows(p):
    keys=[]
    for line in Path(p).read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,*_=line.split();keys.append([int(q),int(b)])
    return sorted(keys)

def audit_runtime(root,states):
    name='runtime236' if states==236 else 'runtime_rotated237'
    receipt=read(root/'evidence'/f'{name}.json');cases=read(root/'evidence'/f'{name}_cases.json')
    sites=read(root/'source/sites_logical.json')
    expected=[(i,pos) for i,x in enumerate(sites) for pos in ((False,True) if x[1]=='CD' else (False,))]
    require(len(cases)==len(expected)==8386,'Incomplete supplied case array')
    require(receipt['status']=='UNIVERSAL_MATHEMATICAL_PASS','Missing full runtime pass')
    require(receipt['table_sha256']==PINS['machines/zfc236_old.tm' if states==236 else 'machines/zfc_rotated237_old.tm'],'Runtime table pin')
    require(receipt['sites_sha256']==PINS['source/sites_logical.json'],'Runtime source pin')
    for c,key in zip(cases,expected):
        require(type(c['site_index']) is int and type(c['positive']) is bool,'Invalid guard key')
        require((c['site_index'],c['positive'])==key,'Guard order mismatch')
        require(len(c['duration'])==len(c['motion'])==13,'Invalid affine dimension')
        require(all(type(x) is int and x>=0 for x in c['duration']) and c['duration'][0]>=1,'Nonpositive clock')
        require(all(type(x) is int for x in c['motion']),'Invalid motion')
        require(type(c['symbolic_steps']) is int and c['symbolic_steps']>0,'Invalid rule count')
        require(set(c['kinds'])<={'literal','unary','list'} and sum(c['kinds'].values())==c['symbolic_steps'],'Rule census mismatch')
    total=sum(c['symbolic_steps'] for c in cases)
    require(total==receipt['symbolic_steps']==(2267815 if states==236 else 2262455),'Wrong aggregate runtime rules')
    require(min(c['duration'][0] for c in cases)==13,'Wrong minimum clock')
    table=root/'machines'/('zfc236_old.tm' if states==236 else 'zfc_rotated237_old.tm')
    require(receipt['directly_used_rows']==table_rows(table),'Incomplete literal row coverage')
    if states==236:
        require(receipt['working_states']==236 and receipt['transition_rows']==472,'Final table census')
        for field,path in [('checker_sha256','verification/verify_runtime.py'),('engine_sha256','upstream/zfc237/verification/symbolic_runtime.py'),('helper_sha256','upstream/zfc237/verification/independent_runtime.py')]:
            require(receipt[field]==digest(root/path),'Runtime code provenance mismatch: '+field)
    else:
        # Retain the original discovery-time schema; do not relabel it as
        # execution of the newer packaged wrapper.
        require(receipt['states']==237 and receipt['replayed']==8386 and receipt['reused']==0,'Basis replay scope')
        require(receipt['startup_steps']==409835 and receipt['startup_complete_configuration_identical'],'Basis startup')
    return {'status':'AUDITED_STORED_UNIVERSAL_RECEIPT','states':states,'cases':len(cases),'rules':total,
            'receipt_sha256':digest(root/'evidence'/f'{name}.json'),'case_array_sha256':digest(root/'evidence'/f'{name}_cases.json'),
            'fresh_unbounded_execution':False}

def artifact_checks(root):
    for p,h in PINS.items():require(digest(root/p)==h,'Rebuilt pin mismatch: '+p)
    c=read(root/'machines/construction236.json')
    boot=read(root/'upstream/zfc237/evidence/bootstrap237.json')
    require(c['startup_support']==boot['all_one_positions'],'Exact calibrated startup tape differs')
    require(c['startup_head']==-5 and c['new_startup_steps']==409835 and len(c['startup_support'])==351,'Wrong startup frame')
    require(not c['rotation_startup_visits'] and not c['exceptional_startup_visits'],'Unexpected startup visits')
    # Independently decode the physical register/spare frame and seed.
    ones=set(c['startup_support']);head=c['startup_head'];require(min(ones)==head-1,'Left exterior')
    header=min(x for x in ones if x>=head+64);require(header==176,'Header')
    p=header+1;last=max(ones);values=[]
    while p<=last:
        require(p not in ones and p+1 in ones,'Invalid register block');p+=1;begin=p
        while p in ones:p+=1
        values.append(p-begin-1)
    require(p==last+1 and values[:9]==[0,0,0,3,0,0,3,0,0] and values[9:]==[1]*167,'Wrong seed/spares')
    numbering=read(root/'machines/renumbering236.json')['old_to_new']
    rows=table_rows(root/'machines/zfc236.tm')
    require(rows==[[q,b] for q in range(236) for b in (0,1)],'Canonical state set')
    # Graph reachability is only a census check, never a halting claim.
    table={}
    for line in (root/'machines/zfc236.tm').read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,z=line.split();table[int(q),int(b)]=int(z)
    live=set();todo=[0]
    while todo:
        q=todo.pop()
        if q in live:continue
        live.add(q)
        if q!=236:todo.extend((table[q,0],table[q,1]))
    require(live==set(range(237)),'Unexpected graph-unreachable state')
    return {'status':'PASS_REBUILT_ARTIFACTS_AND_EXACT_CALIBRATED_SEED','states':236,'all_working_states_graph_reachable':True,
            'startup_steps':409835,'one_cells':351,'header':176,'gap_parameter':117,'physical_values':values[:9],'spare_count':167,
            'canonical_dispatcher':numbering['96']}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--full',action='store_true')
    ap.add_argument('--output-dir',type=Path,default=ROOT/'replay');a=ap.parse_args()
    require(sys.version_info>=(3,10) and __debug__ and not sys.flags.optimize,'Python3.10+ with assertions is required')
    out=a.output_dir.resolve();require(not out.exists() or not any(out.iterdir()),'Choose a new or empty output directory')
    entries,mc=manifest(ROOT);out.mkdir(parents=True,exist_ok=True);began=time.monotonic()
    result={'status':'RUNNING','full':a.full,'manifest':mc,'runtime_audits':[audit_runtime(ROOT,n) for n in (236,237)],'jobs':[]}
    write(out/'replay.json',result)
    with tempfile.TemporaryDirectory(prefix='zfc236-replay-') as temp:
        work=Path(temp)/'package';work.mkdir()
        for name in entries:
            p=work/name;p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(ROOT/name,p)
        shutil.copy2(ROOT/'SHA256SUMS',work/'SHA256SUMS')
        env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
        def job(name,args):
            cmd=[sys.executable,'-B',*map(str,args)];start=time.monotonic();log=out/(name+'.log')
            with log.open('w') as f:p=subprocess.run(cmd,cwd=work,env=env,stdout=f,stderr=subprocess.STDOUT)
            r={'name':name,'argv':[str(x).replace(str(work),'$PACKAGE') for x in cmd],'returncode':p.returncode,'seconds':time.monotonic()-start,'log':log.name}
            print(name,'PASS' if p.returncode==0 else 'FAIL',round(r['seconds'],2),'seconds',flush=True)
            require(p.returncode==0,'Failed job '+name+'; see '+str(log));return r
        seq=[
          ('construction',['build_zfc236.py','--input237','upstream/zfc237/zfc_composed237_old.tm','--output-dir','machines']),
          ('source',['build_source.py']),
          ('source_independent',['verification/check_source_rotation.py','--source','source/boundary_source_input.json','--baseline-table','upstream/zfc237/zfc_composed237_old.tm','--rotated-table','machines/zfc_rotated237_old.tm','--rotated-sites','source/sites_logical.json','--output','source/independent_replay.json']),
          ('fold_independent',['verification/check_fold236.py']),
          ('fold_generic',['verification/verify_state_fold.py','machines/zfc_rotated237_old.tm','machines/zfc236_old.tm','--keep','182','--drop','223','--output','evidence/fold236_generic.json']),
          ('generic_adversarial',['formalisms/check_fold_checker_regressions.py','--checker','verification/verify_state_fold.py']),
          ('equational688',['formalisms/build_e688.py']),
          ('tail_countermodel',['formalisms/check_tail_deletion_model.py']),
          ('inherited237_quick',['upstream/zfc237/reproduce.py','--output-dir',out/'inherited237']),
        ]
        try:
            for name,args in seq:result['jobs'].append(job(name,args));write(out/'replay.json',result)
            result['artifact_checks']=artifact_checks(work)
            if a.full:
                fulljobs=[('runtime236_fresh',['verification/verify_runtime.py','--output',out/'runtime236.json']),
                          ('runtime237_fresh',['verification/verify_runtime.py','--table','machines/zfc_rotated237_old.tm','--states','237','--output',out/'runtime237.json'])]
                with ThreadPoolExecutor(max_workers=2) as ex:
                    futures=[ex.submit(job,n,args) for n,args in fulljobs]
                    for f in futures:result['jobs'].append(f.result())
                for n,count in ((236,2267815),(237,2262455)):
                    r=read(out/f'runtime{n}.json')
                    require(r['status']=='UNIVERSAL_MATHEMATICAL_PASS' and r['cases']==8386 and r['symbolic_steps']==count,'Fresh runtime mismatch')
            for src in ('machines/construction236.json','source/source_certificate.json','evidence/fold236_generic.json','evidence/fold236_independent.json','formalisms/generated/verification.json','formalisms/generated/tail_deletion_checks.json'):
                p=out/'replayed_receipts'/src;p.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(work/src,p)
            result['status']='PASS_FULL_REPLAY' if a.full else 'PASS_QUICK_REPLAY'
            result['fresh_unbounded_jobs']=2 if a.full else 0
        except Exception as ex:
            result['status']='FAIL';result['error']=str(ex);result['traceback']=traceback.format_exc();raise
        finally:
            result['seconds']=time.monotonic()-began;write(out/'replay.json',result)
    print(json.dumps({k:v for k,v in result.items() if k not in ('jobs','runtime_audits')},indent=2))

if __name__=='__main__':main()
