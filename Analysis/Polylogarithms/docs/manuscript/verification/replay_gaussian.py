"""Restore delivered filenames in isolated scratch trees and replay continuations.

Historical source packages are read-only inputs. --part selects independent runs.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, shutil, subprocess, sys
B=Path(__file__).resolve().parents[1]
S=B.parent/'reports/gaussian-parity-reductions'
ap=argparse.ArgumentParser();ap.add_argument('--part',choices=['14','16','17','18','19','19b'],required=True)
a=ap.parse_args();root=B/'verification/.scratch-gaussian'/a.part
out=B/'verification/gaussian-replay'/a.part
root.mkdir(parents=True,exist_ok=True);out.mkdir(parents=True,exist_ok=True)
manifest={}
def copy(source,target):
    p=S/source;dest=root/target;dest.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(p,dest);manifest[source]=hashlib.sha256(p.read_bytes()).hexdigest()
def run(program,*args):
    result=subprocess.run([sys.executable,str(root/program),*args],cwd=root,capture_output=True,text=True)
    (out/(Path(program).stem+'-run.txt')).write_text(result.stdout+result.stderr,encoding='utf-8')
    if result.returncode:raise RuntimeError(f'{program} exited {result.returncode}; see transcript')
if a.part=='14':
    mapping={'run_checks.py':'run_checks.py','shuffle_certificates.py':'shuffle_certificates.py',
     'depth-verify_depth.py':'depth/verify_depth.py','ladders-verify_ladders.py':'ladders/verify_ladders.py',
     'moments-certify_cubic.py':'moments/certify_cubic.py'}
    for source,target in mapping.items():copy('code/14-exact-reductions-'+source,'code/'+target)
    copy('data/14-exact-reductions-moments-cubic_certificate.json','code/moments/cubic_certificate.json')
    (root/'data').mkdir(exist_ok=True)
    run('code/shuffle_certificates.py','--max-weight','9','--output',str(root/'data/shuffle_verification.json'))
    def exact_module(name,path):
        spec=importlib.util.spec_from_file_location(name,root/path)
        m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m)
        return m.exact_checks()
    exact=dict(depth=exact_module('gaussian_depth','code/depth/verify_depth.py'),
               ladders=exact_module('gaussian_ladders','code/ladders/verify_ladders.py'))
    expected=json.loads((root/'code/moments/cubic_certificate.json').read_text())
    run('code/moments/certify_cubic.py','--order','360','--digits','130')
    actual=json.loads((root/'code/moments/cubic_certificate.json').read_text())
    assert actual==expected
    exact['cubic_reference_reproduced_exactly']=True
    (root/'data/exact-summary.json').write_text(json.dumps(exact,indent=2)+'\n',encoding='utf-8')
    run('code/depth/verify_depth.py')
    run('code/ladders/verify_ladders.py','--digits','100','200','--output',str(root/'data/ladder-diagnostics.json'))
    results=[*sorted((root/'data').glob('*.json')),root/'code/depth/depth_results.json',root/'code/moments/cubic_certificate.json']
elif a.part=='16':
    for name in ['verify.py','certified.py','derive_identities.py','test_arithmetic.py']:
        copy('code/16-gaussian-certified-'+name,'code/'+name)
    for d in ['data','generated']:(root/d).mkdir(exist_ok=True)
    run('code/test_arithmetic.py');run('code/verify.py')
    results=sorted((root/'data').glob('*.json'))
elif a.part=='18':
    for name in ['verify.py','gaussian.py','full_ds.py','numerics.py']:
        copy('code/18-signed-kernels-'+name,'code/'+name)
    (root/'data').mkdir(exist_ok=True)
    run('code/verify.py','--terms','400','--max-weight','16','--rank-max','31')
    run('code/numerics.py')
    results=sorted((root/'data').glob('*.json'))
elif a.part=='19':
    for name in ['verify.py','holder.py','identities.py','replay_certificates.py']:
        copy('code/19-gaussian-proofs-'+name,'code/'+name)
    (root/'results').mkdir(exist_ok=True)
    run('code/verify.py','--bits','384')
    run('code/replay_certificates.py')
    results=sorted((root/'results').glob('*.json'))

elif a.part=='19b':
    for name in ['one_two_identities.py','derive_rows.py','verify_coefficients.py','sixth_root.py']:
        copy('code/19-gaussian-proofs-independent-one_two-'+name,'code/independent/one_two/'+name)
    resultsdir=root/'results/independent/one_two';resultsdir.mkdir(parents=True,exist_ok=True)
    run('code/independent/one_two/derive_rows.py','--outdir',str(resultsdir))
    run('code/independent/one_two/verify_coefficients.py','--coefficients',str(resultsdir/'coefficients.json'),'--output',str(resultsdir/'coefficient_verification.json'))
    run('code/independent/one_two/one_two_identities.py','--digits','100','--output',str(resultsdir/'one_two_checks.json'))
    run('code/independent/one_two/sixth_root.py','--digits','100','--output',str(resultsdir/'sixth_root_checks.json'))
    results=sorted(resultsdir.glob('*.json'))

else:
    for name in ['gap_reduce.py','certify.py','symbolic_checks.py']:
        copy('code/17-gap-reductions-'+name,'code/'+name)
    for d in ['verification','data','generated']:(root/d).mkdir(exist_ok=True)
    run('code/symbolic_checks.py');run('code/certify.py')
    results=sorted((root/'verification').glob('*.json'))
for p in results:shutil.copyfile(p,out/p.name)
(out/'replay-summary.json').write_text(json.dumps(dict(part=a.part,source_files=manifest,
 result_files=[p.name for p in results],all_programs_exited_zero=True,
 scope='Exact certificates and explicitly distinguished numerical diagnostics; no conjecture proved by residual enclosure.'),indent=2)+'\n',encoding='utf-8')
print('Continuation',a.part,'completed;',len(results),'fresh result files.')
