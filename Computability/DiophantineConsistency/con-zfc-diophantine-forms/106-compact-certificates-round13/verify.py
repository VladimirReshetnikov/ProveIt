#!/usr/bin/env python3
"""Read-only release verification: all work runs in a temporary clean copy.
The checks prove the stated finite identities, not consistency or a kernel theorem.
Python 3.12+ and SymPy. No network or external repository is accessed.
"""
import argparse,hashlib,json,os,pathlib,platform,shutil,subprocess,sys,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parent

def need(ok,message):
    if not ok: raise RuntimeError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report',type=pathlib.Path,help='Write runtime receipt outside the release directory.')
    args=parser.parse_args()
    if args.report:
        need(not args.report.resolve().is_relative_to(ROOT),'Runtime report must be outside the release directory.')
    import sympy
    started=time.monotonic();manifest=json.loads((ROOT/'MANIFEST.sha256.json').read_text())
    for name,want in manifest.items():
        p=ROOT/name;need(p.is_file(),'Missing release file '+name);need(sha(p)==want,'SHA256 mismatch '+name)
    actual={str(p.relative_to(ROOT))for p in ROOT.rglob('*')if p.is_file() and '__pycache__'not in p.parts and p.name!='MANIFEST.sha256.json'}
    need(actual==set(manifest),'Unexpected or unlisted release payloads.')
    jobs=[]
    with tempfile.TemporaryDirectory(prefix='conzfc-round13-clean-')as t:
        stage=pathlib.Path(t)/'release';shutil.copytree(ROOT,stage,ignore=shutil.ignore_patterns('__pycache__'))
        env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
        def run(label,component,script,flags=(),compare=()):
            ts=time.monotonic();cmd=[sys.executable,*flags,script]
            p=subprocess.run(cmd,cwd=stage/component,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
            need(p.returncode==0,label+' failed:\n'+p.stdout+'\n'+p.stderr)
            for filename in compare:
                need((stage/component/filename).read_bytes()==(ROOT/component/filename).read_bytes(),'Non-deterministic rebuild '+component+'/'+filename)
            item={'label':label,'component':component,'script':script,'optimized':('-O'in flags),'seconds':round(time.monotonic()-ts,3),'returncode':p.returncode,'stdout_sha256':hashlib.sha256(p.stdout.encode()).hexdigest(),'stderr_sha256':hashlib.sha256(p.stderr.encode()).hexdigest(),'byte_compared_files':list(compare)}
            jobs.append(item);print(label+' PASS ('+str(item['seconds'])+' s)',flush=True)
        run('direct deterministic rebuilds normal and optimized','direct','verify_rebuild.py')
        run('direct independent audits normal and optimized','late_direct_audit','run_release.py')
        rfiles=['integer13_degree1072.json','integer14_degree378.json','integer15_degree172.json','integer15c_degree170.json','integer16_degree98.json','METRICS.json']
        nfiles=['integer10_polar.json','integer10_linear.json','integer10_cubic.json','integer10_sixterm.json']
        for mode,flags in [('normal',()),('optimized',('-O',))]:
            run('architecture '+mode,'architecture','check_architecture.py',flags)
            run('radical deterministic rebuild '+mode,'radicals','build.py',flags,rfiles)
            run('radical producer-independent checks '+mode,'radicals','check.py',flags)
            run('centered exact identity '+mode,'radicals','check_center_identity.py',flags)
            run('radical second independent audit '+mode,'radicals_audit','check_radicals.py',flags)
            run('norm deterministic rebuild '+mode,'norm','build.py',flags,nfiles)
            run('norm exact checks '+mode,'norm','check.py',flags)
            run('norm second independent audit '+mode,'norm_audit','independent_checks.py',flags)
            run('twelve-integer deterministic rebuild '+mode,'radicals12','build.py',flags,['integer12_degree2048.json','METRICS.json'])
            run('twelve-integer arithmetic checks '+mode,'radicals12','check.py',flags)
            run('twelve-integer second independent audit '+mode,'radicals12_audit','check_twelve.py',flags)
        direct=json.loads((stage/'direct/CLEAN_REBUILD.json').read_text())
        audits=json.loads((stage/'late_direct_audit/FINAL_REPLAY.json').read_text())
        arch=json.loads((stage/'architecture/CHECKS.json').read_text())
        need(len(jobs)==24,'Driver inventory changed.')
        need(len(audits['runs'])==10,'Direct audit inventory changed.')
        need(sum(r['exact_json_files_compared']for r in direct['runs'])==52,'Direct rebuilt file count changed.')
        need(arch['clean_replayed_variants']==3,'Architecture variant count changed.')
        receipt={'status':'PASS','python':platform.python_version(),'sympy':sympy.__version__,'driver_optimized':not __debug__,'authenticated_files':len(manifest),'top_level_invocations':len(jobs),'direct_internal_audit_invocations':10,'direct_rebuilt_variants_per_mode':5,'direct_byte_comparisons_both_modes':52,'architecture_rebuilt_variants_per_mode':3,'radical_rebuilt_graphs_per_mode':5,'norm_rebuilt_graphs_per_mode':4,'twelve_integer_rebuilt_graphs_per_mode':1,'elapsed_seconds':round(time.monotonic()-started,3),'jobs':jobs,'scope':'Finite exact algebra, literal graph and payload checks, negative controls, and clean deterministic rebuilds. Universal source calibration remains ordinary mathematics, not a new kernel proof.'}
    if args.report:args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
