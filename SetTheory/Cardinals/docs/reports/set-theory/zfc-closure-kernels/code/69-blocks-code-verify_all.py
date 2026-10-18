#!/usr/bin/env python3
"""Portable verification of the research contribution; no network required.

Large discovery searches are not rerun by this driver. The positive reference
checks run on a disposable copy so the attributed reference stays unchanged.
"""
from pathlib import Path
import json,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parents[1]
RESULTS=ROOT/'results'
JOBS=[]

def job(name,script,*args):
    began=time.monotonic()
    proc=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],
        cwd=ROOT,text=True,capture_output=True)
    (RESULTS/(name+'.log')).write_text(proc.stdout+proc.stderr)
    assert proc.returncode==0,(name,proc.stdout[-1500:],proc.stderr[-1500:])
    JOBS.append(dict(name=name,status='PASS',seconds=round(time.monotonic()-began,3)))
    print('PASS',name,flush=True)

def invariants():
    import source_abstract_invariant as G
    import source_invariant_affine as S
    import source_exactroot_affine as E
    from source_constant_domains import Domain,facts
    from program import site_map,lookup
    general,n=G.solve((7,)*9)
    assert general==S.INVARIANT
    assert G.check((7,)*9,general)==8384
    z0,dead0,guards0=facts(general)
    assert len(z0)==5518 and len(dead0)==4 and len(guards0)==2
    comparison=[]
    for k in (2,4,8,16):
        d=Domain(k);inv,iterations=d.solve()
        assert d.check(inv)==8384
        zero,dead,guards=facts(inv)
        assert len(inv)==6456 and len(zero)==5551
        assert dead==dead0 and guards==guards0 and z0<=zero
        if k==4:assert inv==E.INVARIANT
        comparison.append(dict(K=k,reachable_leaves=len(inv),exact_zero_facts=len(zero),
            new_zero_facts=len(zero-z0),unreachable_leaves=len(dead),impossible_guards=len(guards)))
    assert E.INVARIANT[lookup('')[0]]==(30,31,31,1,31,31,1,1,31)
    out=dict(status='PASS',general_zero_facts=len(z0),nonhalting_transfers=8384,
        source_leaves=len(site_map),comparisons=comparison)
    (RESULTS/'invariants-rechecked.json').write_text(json.dumps(out,indent=2)+'\n')
    JOBS.append(dict(name='source_invariant_recomputation',status='PASS'))
    print('PASS source_invariant_recomputation',flush=True)

def quiet():
    import common as C
    import source_block_affine as Q
    import source_exactroot_block_affine as E
    records=[]
    for label,checker in (('general',Q),('exact',E)):
        count=total=expanded=maximum=0
        for pc,branch,target,halt in C.cases:
            if not checker.case_allowed(pc,branch):continue
            ends=checker.endpoints(pc,branch)
            checker.run(C.T,pc,branch,target,halt=halt,fuel=1000)
            count+=1;total+=len(ends);expanded+=len(ends)>1
            maximum=max(maximum,len(ends))
            if label=='exact':
                # The stricter invariant can add post-leaf zero facts.
                # The accepted tape endpoints and source lengths coincide.
                project=lambda xs:tuple((e['affine_target'],e['source_steps']) for e in xs)
                assert project(ends)==project(Q.endpoints(pc,branch))
        assert (count,total,expanded,maximum)==(8385,10563,2050,5)
        records.append(dict(scope=label,cases=count,total_endpoints=total,
            expanded_cases=expanded,maximum_source_instructions=maximum))
    (RESULTS/'quiet-blocks-rechecked.json').write_text(json.dumps(dict(status='PASS',records=records),indent=2)+'\n')
    JOBS.append(dict(name='quiet_block_replays',status='PASS'))
    print('PASS quiet_block_replays',flush=True)

def recorded_domain_comparison():
    names=('incoming-action-results.json','invariant-incoming-action-results.json',
        'quiet-incoming-action-results.json','workspace-incoming-action-results.json',
        'workspace-block-incoming-action-results.json','arithmetic-incoming-action-results.json')
    records=[json.loads((RESULTS/name).read_text()) for name in names]
    assert all(r['tested']==254856 for r in records)
    assert all(r['states']==records[0]['states'] for r in records)
    assert sorted(r['state'] for r in records[0]['candidates'])==[30,39,42,67,122,235]
    JOBS.append(dict(name='recorded_domain_identity',status='PASS',
        scope='Compares completed recorded action domains; does not replay the searches.'))
    print('PASS recorded_domain_identity (record comparison)',flush=True)

def main():
    if not __debug__:raise SystemExit('Assertions required; do not use -O or -OO.')
    began=time.monotonic();RESULTS.mkdir(exist_ok=True)
    reference=ROOT/'reference/context246'
    with tempfile.TemporaryDirectory(prefix='zfc-sub246-reference-') as tmp:
        copy=Path(tmp)/'context246'
        shutil.copytree(reference,copy,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        for name in ('check_folds','check_macro_inductions'):
            job('reference_'+name,copy/'code'/(name+'.py'))
        job('reference_review_affine_source',copy/'code/review_affine_source.py',
            '--program',copy/'sources/Prog254.v',
            '--sites',copy/'sources/prior/instruction-sites-physical.json',
            '--table',copy/'machine/zfc_prefix246_old.tm',
            '--checker',copy/'sources/prior/prefix_affine.py',
            '--output',copy/'results/affine-source-review.json')
        job('reference_check_bootstrap',copy/'code/check_bootstrap.py')
    invariants()
    job('source_guard_oracle',ROOT/'code/check_source_invariant_affine.py')
    job('exact_root_guard_oracle',ROOT/'code/check_source_exactroot_affine.py')
    quiet()
    job('workspace_controls',ROOT/'code/check_workspace_affine.py',
        '--output',RESULTS/'relaxed-affine-controls.json')
    job('arithmetic_block_controls',ROOT/'code/check_arithmetic_blocks.py',
        '--output',RESULTS/'arithmetic-block-controls.json')
    job('rejected_tables',ROOT/'code/check_rejected.py')
    job('joint_graph_obstructions',ROOT/'code/verify_union_obstructions.py')
    job('reachable_detector_witness',ROOT/'code/threshold_literal_witness.py')
    recorded_domain_comparison()
    tex=(ROOT/'results.tex').read_text()
    for literal in ('{17,643}','{13}','{4,856}'):assert literal in tex
    out=dict(status='PASS',new_sub246_consistency_machine=False,new_kernel_endpoint=False,
        jobs=JOBS,seconds=round(time.monotonic()-began,3))
    (RESULTS/'verification-summary.json').write_text(json.dumps(out,indent=2)+'\n')
    print('ALL SUB246 RESEARCH CHECKS PASS')
    print('No new sub-246 consistency machine is claimed.')
if __name__=='__main__':main()
