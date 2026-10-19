"""Root-owned persistent substantive replay of the 240-state proposal.

No delivery manifest verification, nested suite execution, search rerun, or
proof compiler. All ten leaf jobs use an unchanged disposable source copy.
"""
from pathlib import Path
import hashlib, json, os, shutil, signal, subprocess, sys, time, zipfile, io

REPO = Path('/home/codex/.codex/worktrees/ec20/Proofs')
SOURCE = Path('/tmp/zfc-intake-e5c2b3337e/zfc240-source-rotation-20261018')
OUT = Path('/tmp/zfc-intake-e5c2b3337e/replay1')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
enc = lambda x: json.dumps(x, indent=2, ensure_ascii=False)+'\n'
def load(p): return json.loads(Path(p).read_bytes())

def main():
    assert __debug__ and not OUT.exists()
    original = {str(p.relative_to(SOURCE)):sha(p) for p in SOURCE.rglob('*') if p.is_file()}
    assert len(original) == 79
    archive = subprocess.check_output(['git','show','8c41b1fb7d7bb8cd0612e37848181fe4a2f5d569:docs/incoming/BusyBeaver_241_Companion_2026-10-18.zip'],cwd=REPO)
    assert archive == (SOURCE/'reference/BusyBeaver_241_Companion_2026-10-18.zip').read_bytes()
    bindings = {'reference/baseline241_old.tm':'runtime/candidate_1_old.tm',
                'reference/baseline_sites.json':'runtime/sites_logical.json',
                'reference/upstream_symbolic_runtime.py':'runtime/symbolic_runtime.py',
                'reference/upstream_independent_runtime.py':'runtime/independent_runtime.py'}
    with zipfile.ZipFile(io.BytesIO(archive)) as z:
        for local, prior in bindings.items():
            assert (SOURCE/local).read_bytes() == z.read('busybeaver241-companion/'+prior)
    before = (SOURCE/'reference/upstream_symbolic_runtime.py').read_bytes()
    changes = [(b'len(sites)==6459',b'len(sites)==6455'),
      (b'3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4',b'74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d'),
      (b'exact_QT_source_pin',b'exact_rotated_source_pin')]
    for old,new in changes:
        assert before.count(old)==1
        before=before.replace(old,new)
    assert before == (SOURCE/'verification/symbolic_runtime.py').read_bytes()
    assert (SOURCE/'verification/independent_runtime.py').read_bytes() == (SOURCE/'reference/upstream_independent_runtime.py').read_bytes()
    prior = Path('/tmp/zfc-intake-8c41b1fb7d/fresh-replay-1/result.json')
    assert sha(prior)=='45441fc801c89a91f3f8fb313bb811f2de23c1bb65f463fba70348d11e6e9d3b'
    assert load(prior)['status']=='ROOT_SUBSTANTIVE_LEAF_REPLAY_PASS'
    OUT.mkdir(); package=OUT/'package';shutil.copytree(SOURCE,package)
    fresh=OUT/'fresh';fresh.mkdir();logs=OUT/'logs';logs.mkdir()
    record={'status':'RUNNING','root_script':{'path':__file__,'sha256':sha(__file__)},
      'source':str(SOURCE),'unchanged_copy':str(package),'source_identities':original,
      'inherited_archive_git_binding':'8c41b1fb7d7bb8cd0612e37848181fe4a2f5d569',
      'inherited_four_exact_bindings':bindings,'runtime_adapter_changes':[[a.decode(),b.decode()] for a,b in changes],
      'prior_substantive_replay':{'path':str(prior),'sha256':sha(prior)},
      'manifest_contents_checked':False,'nested_predecessor_suites_repeated':False,
      'jobs':[],'scope':'Fresh exact construction, source graph, local tape proofs, startup, infinite-model filter and two complete unary/list runtime checks; ordinary mathematical evidence, not a Lean or PA endpoint.'}
    def save(): (OUT/'result.json').write_text(enc(record))
    def unchanged():
        for root in [SOURCE,package]:
            assert {str(p.relative_to(root)):sha(p) for p in root.rglob('*') if p.is_file()}==original
    env=dict(os.environ,PYTHONOPTIMIZE='',PYTHONDONTWRITEBYTECODE='1',B245_INPUTS=str(package/'reference'),B245_OUTPUT=str(fresh))
    env.pop('PYTHONPATH',None)
    def run(name,script,args,expect):
        cmd=[sys.executable,'-B',str(package/script),*map(str,args)]
        log=logs/(name+'.log');began=time.monotonic();job={'name':name,'command':cmd,'status':'RUNNING','log':str(log)}
        record['jobs'].append(job);save();print('Running '+name,flush=True)
        with log.open('wb') as capture:
            proc=subprocess.Popen(cmd,cwd=(package/script).parent,env=env,stdout=capture,stderr=subprocess.STDOUT,start_new_session=True)
            timed_out=False
            try: code=proc.wait(timeout=1200)
            except BaseException as ex:
                timed_out=isinstance(ex,subprocess.TimeoutExpired)
                try: os.killpg(proc.pid,signal.SIGKILL)
                except ProcessLookupError: pass
                code=proc.wait();job['interruption']=repr(ex)
        job.update(exit_code=code,timed_out=timed_out,seconds=time.monotonic()-began,log_sha256=sha(log))
        save();assert code==0 and not timed_out,(name,job)
        for p,status in expect.items():assert load(p)['status']==status,(name,p)
        unchanged();job['status']='PASS';save()
    save()
    try:
        v=Path('verification')
        run('build',Path('build.py'),['--output',fresh/'build.json'],{fresh/'build.json':'BUILD_EXACT_RECONSTRUCTION_PASS'})
        run('local-root',v/'verify_local.py',['--output',fresh/'local_root.json'],{fresh/'local_root.json':'ROOT_INDEPENDENT_LOCAL_ALL_TAPE_PASS'})
        run('boot-root',v/'verify_boot.py',['--output',fresh/'boot_root.json'],{fresh/'boot_root.json':'ROOT_EXACT_BLANK_AND_CLOCK_PASS'})
        run('local-independent',v/'verify_local_independent.py',['--root',package,'--output',fresh/'local_independent.json'],{fresh/'local_independent.json':'PASS_FINITE_LOCAL_ALL_TAPE_241_ROTATED_TO_240'})
        run('boot-independent',v/'verify_boot_independent.py',['--root',package,'--output',fresh/'boot_independent.json'],{fresh/'boot_independent.json':'PASS_EXACT_240_BLANK_SPARSE_DENSE'})
        run('source',v/'verify_source.py',['--package-root',package,'--output-dir',fresh/'source'],{fresh/'source/rotation142_source_proof.json':'SOURCE_CONTEXT_ROTATION142_PASS',fresh/'source/rotation142_boot.json':'ROTATION142_EXACT_BLANK_PASS'})
        run('independent-review',v/'review_independent.py',['--root',package,'--output',fresh/'review_independent.json'],{fresh/'review_independent.json':'INDEPENDENT_SOURCE_AND_LOCAL_REVIEW_PASS'})
        run('theory',Path('theory/dense_order_filter.py'),['--output',fresh/'dense_order_results.json'],{fresh/'dense_order_results.json':'PASS'})
        assert load(fresh/'dense_order_results.json')==load(SOURCE/'evidence/dense_order_results.json')
        assert load(fresh/'local_root.json')['invariant_implications']==7640
        assert load(fresh/'local_independent.json')['positive_whole_tape_blocks']==7640
        assert load(fresh/'boot_root.json')['new_steps']==409691
        assert load(fresh/'source/rotation142_source_proof.json')['outside_guarded_edges']==8370
        runtime=[]
        for name,table,states in [('rotated241','reference/rotated241_old.tm',241),('final240','machines/zfc240_old.tm',240)]:
            output=fresh/(name+'.json')
            run(name,v/'symbolic_runtime.py',['--table',package/table,'--sites',package/'machines/sites_logical.json','--output',output],{output:'UNIVERSAL_MATHEMATICAL_PASS'})
            r=load(output);cases=load(fresh/(name+'_cases.json'))
            assert r['cases']==r['expected_cases']==len(cases)==8386
            assert r['input_validation']['working_states']==states and r['input_validation']['leaf_count']==6455
            assert r['minimum_actual_steps']==min(c['duration'][0] for c in cases)==13
            assert r['symbolic_steps']==sum(c['symbolic_steps'] for c in cases)
            keys={(int(line.split()[0]),int(line.split()[1])) for line in (package/table).read_text().splitlines() if line and not line.startswith('#')}
            assert set(map(tuple,r['directly_used_rows']))==keys and len(keys)==states*2
            assert r['table_sha256']==sha(package/table) and r['sites_sha256']==sha(package/'machines/sites_logical.json')
            assert r['checker_sha256']==sha(package/v/'symbolic_runtime.py') and r['helper_sha256']==sha(package/v/'independent_runtime.py')
            if name=='final240':
                assert r['symbolic_steps']==2322575
                assert (fresh/'final240_cases.json').read_bytes()==(SOURCE/'evidence/runtime240_cases.json').read_bytes()
                sealed=load(SOURCE/'evidence/runtime240.json')
                for key in ['blocks','input_validation','directly_used_rows','symbolic_steps','minimum_actual_steps']:
                    assert r[key]==sealed[key],key
            runtime.append({'name':name,'status':r['status'],'cases':r['cases'],'rules':r['symbolic_steps'],'rows':len(keys),'seconds':r['seconds'],'record':str(output),'sha256':sha(output)})
        unchanged();record.update(status='ROOT_TEN_SUBSTANTIVE_JOBS_PASS',runtime=runtime,all_inputs_unchanged=True,full_final_case_array_matches_delivery=True)
    except BaseException as ex:
        record.update(status='FAIL',error=repr(ex));save();raise
    save();print(enc({'status':record['status'],'jobs':len(record['jobs']),'runtime':runtime}),flush=True)

if __name__=='__main__':main()
