#!/usr/bin/env python3
"""Portable replay; every generated file stays in a temporary directory.

Manual commands, after compiling affine_screen.cpp:
  python3 affine_acceleration.py
  python3 verify_source_examples.py
  python3 verify_records.py --output independent-record-replay.json
  python3 composed_rotations.py --all-first --fast --verify --graph-max 253 --seconds 3600
  python3 rebase_rotations.py --seconds 3600
  python3 composed_rotations.py --graph-max 245 --seconds 3600  # inherited 40 ties
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time

HERE=Path(__file__).resolve().parent

def read(path):return json.loads(path.read_text())

def identities():
    manifest=read(HERE/'vendor-manifest.json')
    for row in manifest:
        path=HERE/row['path']
        assert path.is_relative_to(HERE) and path.is_file(),row
        assert hashlib.sha256(path.read_bytes()).hexdigest()==row['sha256'],row['path']
    return len(manifest)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full',action='store_true',help='Also regenerate both complete restricted censuses.')
    ap.add_argument('--output',type=Path,help='Write a compact result to this path after success.')
    a=ap.parse_args()
    if not __debug__:raise RuntimeError('Run Python without -O: assertions are verification conditions.')
    compiler=shutil.which('g++')
    if compiler is None:raise RuntimeError('A C++17-capable g++ is required.')
    count=identities();started=time.monotonic()
    expected_double=read(HERE/'double_all_fast/results.json')
    expected_rebase=read(HERE/'rebased/results.json')
    expected_replay=read(HERE/'independent-witness-replay.json')
    parent=os.environ.get('ZFC_DECODER_TEMP_PARENT')
    with tempfile.TemporaryDirectory(prefix='decoder-replay-',dir=parent) as td:
        work=Path(td)/'decoder'
        shutil.copytree(HERE,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc','*.so','*.ii','*.s','*.o','*.log','*.tmp'))
        env=os.environ.copy();env.pop('ZFC_DECODER_VENDOR',None);env.pop('PYTHONOPTIMIZE',None)
        def run(name,args):
            print('Checking '+name+' ...',flush=True)
            with (work/(name+'.log')).open('w') as log:
                result=subprocess.run(args,cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT)
            if result.returncode:
                tail=(work/(name+'.log')).read_text(errors='replace')[-16000:]
                raise RuntimeError(name+' failed:\n'+tail)
        run('compile',[compiler,'-O3','-std=c++17','-save-temps=obj','-shared','-fPIC','affine_screen.cpp','-o','affine_screen.so'])
        run('baseline',[sys.executable,'affine_acceleration.py'])
        baseline=read(work/'acceleration-control.json')
        assert baseline['status']=='PASS_DISCOVERY_CONTROLS'
        assert [baseline[k] for k in ('baseline_sites','guarded_cases','baseline_used_rows','baseline_used_states')]==[6460,8391,492,246]
        assert len(baseline['negative_controls'])==3
        run('source-examples',[sys.executable,'verify_source_examples.py'])
        examples=read(work/'source-rebase-independent.json')
        assert examples['status']=='PASS_INDEPENDENT_LITERAL_PATH_WALK'
        assert len(examples['examples'])==7 and examples['total_checked_successor_edges']==58730
        run('independent-records',[sys.executable,'verify_records.py','--output','independent-record-replay.json'])
        replay=read(work/'independent-record-replay.json')
        assert replay['status']=='PASS_INDEPENDENT_PYTHON_REPLAY'
        assert replay['counts']==expected_replay['counts'],(replay['counts'],expected_replay['counts'])
        if a.full:
            run('double-census',[sys.executable,'composed_rotations.py','--all-first','--fast','--verify','--graph-max','253','--seconds','3600'])
            double=read(work/'double_all_fast/results.json')
            assert not double['counts'].get('time_limit_hit'),double['counts']
            assert double['counts']==expected_double['counts'],(double['counts'],expected_double['counts'])
            assert double['records']==expected_double['records'],'Regenerated compact records differ'
            run('rebased-census',[sys.executable,'rebase_rotations.py','--seconds','3600'])
            rebase=read(work/'rebased/results.json')
            assert not rebase['counts'].get('time_limit_hit'),rebase['counts']
            assert rebase['counts']==expected_rebase['counts'],(rebase['counts'],expected_rebase['counts'])
            assert len(rebase['records'])==304
            fields=('recipe','node','rotation','control_policy','signature','recycle','generic','status')
            assert [[r[k] for k in fields] for r in rebase['records']]==[[r[k] for k in fields] for r in expected_rebase['records']]
        out=dict(status='PASS_PORTABLE_DECODER_REPLAY',full_censuses_regenerated=a.full,
                 imported_files_verified=count,baseline_guarded_cases=8391,
                 independently_checked_source_edges=58730,independent_classifications=replay['counts'],
                 double_census_counts=expected_double['counts'],rebasing_census_counts=expected_rebase['counts'],
                 elapsed=time.monotonic()-started,
                 scope='Complete restricted research replay. No sub246 construction or global lower bound is claimed.')
    if a.output:
        a.output.parent.mkdir(parents=True,exist_ok=True)
        a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
