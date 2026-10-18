#!/usr/bin/env python3
"""Reproduce the exact quick checks, optionally rerunning expanded induction."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time

ROOT=Path(__file__).resolve().parents[1]
CRITICAL={
 'reference/zfc_combined243_old.tm':'4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300',
 'reference/zfc_combined243.tm':'a3860fb49d6b96e58ead6293134f246d59b3958231cb56850273c4b8a8138791',
 'machine/zfc_context242_old.tm':'6b700aa713418cfe347a6ff2d0a92de7c31810d1cf69814b4684c7fb463876a0',
 'machine/zfc_context242.tm':'64ddeb2c01c3e9c7feffaffaad87266a270716c9307892a0445bf869b988984d',
 'machine/sites_logical.json':'3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4',
 'machine/sites_physical.json':'ee14a4496cc216de7c242f5e652de47d455169d79856ba36bee3a4fc3d69d86a',
 'reference/reproduction-reference.json':'2d7710b02b200a1f0641fb9bb72fc0a881230f9bef0ca7ebd1164e53a31689ba',
}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())

def inputs():
    out={}
    for rel,h in CRITICAL.items():
        p=ROOT/rel;assert p.is_file() and not p.is_symlink() and digest(p)==h,rel
        out[rel]=h
    index=load(ROOT/'reference/reproduction-reference.json')
    assert len(index['files'])==291
    for row in index['files']:
        rel='reference/baseline245/'+row['path'];p=ROOT/rel
        assert '..' not in Path(row['path']).parts and not Path(row['path']).is_absolute()
        assert p.is_file() and not p.is_symlink() and p.stat().st_size==row['bytes']
        assert digest(p)==row['sha256'],rel
        out[rel]=row['sha256']
    for p in sorted((ROOT/'code').glob('*.py')):
        out[str(p.relative_to(ROOT))]=digest(p)
    out['machine/renumbering.json']=digest(ROOT/'machine/renumbering.json')
    return out

def runtime_record(name,expanded):
    p=ROOT/'evidence'/name;j=load(p)
    status='PASS_UNIVERSAL_EXPANDED_RUNTIME' if expanded else 'PASS_UNIVERSAL_AFFINE_RUNTIME'
    assert j['status']==status and j['complete'] and j['source_leaves']==6459
    assert j['expected_cases']==j['counts']['cases']==len(j['cases'])==8390
    assert j['frame_padding']==64 and j['arbitrary_primary_registers']
    assert j['arbitrary_nonempty_finite_spare_suffix'] and j['positive_progress_checked']
    assert j['table_sha256']==CRITICAL['machine/zfc_context242_old.tm']
    assert j['sites_logical_sha256']==CRITICAL['machine/sites_logical.json']
    sites=load(ROOT/'machine'/('sites_logical.json' if expanded else 'sites_physical.json'))
    expected=[(i,p,op,r,z) for i,(p,op,r) in enumerate(sites) for z in ((True,False) if op=='CD' else (None,))]
    assert [(c['index'],c['pc'],c['op'],c['r'],c['zero']) for c in j['cases']]==expected
    key='time_lower_bound' if expanded else 'minimum_literal_steps'
    assert all(c[key]>0 for c in j['cases'])
    if expanded:
        assert j['literal_rows_covered']==484 and j['unused_rows']==[]
    return {'sha256':digest(p),'status':status,'cases':8390,'counts':j['counts']}

def main():
    if not __debug__: raise RuntimeError('Run with Python assertions enabled.')
    ap=argparse.ArgumentParser(description=__doc__)
    modes=ap.add_mutually_exclusive_group()
    modes.add_argument('--expanded',action='store_true')
    modes.add_argument('--reuse-expanded',action='store_true',help='Check a preexisting expanded output without claiming a fresh execution.')
    a=ap.parse_args();before=inputs();commands=[]
    def run(label,args,limit=120):
        cmd=[sys.executable,'-I','-B',str(ROOT/'code'/args[0]),*args[1:]]
        start=time.monotonic()
        with (ROOT/'evidence'/(label+'.stdout.log')).open('wb') as out,(ROOT/'evidence'/(label+'.stderr.log')).open('wb') as err:
            p=subprocess.run(cmd,cwd=ROOT,stdout=out,stderr=err,timeout=limit)
        commands.append({'label':label,'arguments':args,'returncode':p.returncode,'seconds':time.monotonic()-start})
        assert p.returncode==0,(label,p.returncode)
    run('local',['verify_local.py'])
    run('blank',['verify_blank.py'])
    run('affine',['verify_runtime.py'])
    run('literal',['verify_literal.py','--candidate',str(ROOT/'machine')])
    if a.expanded:run('expanded',['verify_runtime.py','--expanded'],900)
    local=load(ROOT/'evidence/independent-local-proof.json')
    assert local['status']=='PASS_INDEPENDENT_LOCAL_PROOF' and local['ordinary_rows']==478
    assert len(local['local_cases'])==5 and local['candidate_sha256']==CRITICAL['machine/zfc_context242_old.tm']
    blank=load(ROOT/'evidence/blank.json')
    assert blank['status']=='PASS_INDEPENDENT_BLANK' and blank['candidate_ticks']==407979 and blank['slow_blocks']==6
    assert blank['sparse_dense_agreement_both_numberings'] and blank['all_other_cells_zero'] and blank['one_count']==351
    literal=load(ROOT/'evidence/literal-regression.json')
    assert literal['status']=='PASS_FINITE_LITERAL_REGRESSION' and literal['cases']==8390
    assert literal['literal_steps']==6473406 and literal['covered_rows']==484 and literal['unused_runtime_rows']==[]
    assert literal['table_sha256']==CRITICAL['machine/zfc_context242_old.tm']
    runtime={'affine':runtime_record('affine-runtime.json',False)}
    if a.expanded or a.reuse_expanded:runtime['expanded']=runtime_record('expanded-runtime.json',True)
    after=inputs();assert before==after,'Verification input changed during replay.'
    result=dict(status='PASS',quick_suite_executed=True,expanded_executed_in_this_run=a.expanded,
        existing_expanded_record_checked=a.reuse_expanded,commands=commands,runtime=runtime,
        input_count=len(before),before=before,after=after,input_postchecks=True,
        proof_assistant_kernel_executed=False,
        scope='Independent local proof plus actual blank/affine/literal execution; expanded execution or preexisting expanded evidence is labeled separately.')
    (ROOT/'evidence/verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('before','after','commands')},indent=2))

if __name__=='__main__':main()
