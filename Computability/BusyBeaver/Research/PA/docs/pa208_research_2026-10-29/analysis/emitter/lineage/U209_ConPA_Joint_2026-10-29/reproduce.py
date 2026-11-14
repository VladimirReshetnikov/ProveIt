#!/usr/bin/env python3
"""Offline, non-mutating release replay. Python 3.10+ standard library only."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(ROOT/'code'))
from common import need,sha,write_json

def hashes():
    records=[]
    for line in(ROOT/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1);path=(ROOT/name).resolve()
        need(path.is_relative_to(ROOT)and path.is_file(),'Manifest path')
        need(sha(path.read_bytes())==digest,'Manifest mismatch: '+name);records.append(name)
    need(len(records)==len(set(records)),'Duplicate manifest entry');return len(records)

def binding():
    import zipfile
    archive=ROOT/'baseline/selected_U212.zip'
    need(sha(archive.read_bytes())=='b5a5d19531f49b05aaad4e1b0f86d6f0de96c37b40a3617522b0d920cf83d6c6','Dependency archive identity')
    with zipfile.ZipFile(archive)as z:
        pre='U212_ConPA_Stacked_2026-10-28/'
        for local,member in[('baseline/u212.native.tm','machine/u212.native.tm'),('baseline/sites.json','machine/sites.json'),
          ('baseline/legacy_mapping.json','inputs/legacy_mapping.json'),('code/symbolic_runtime.py','code/vendor/symbolic_runtime.py'),
          ('code/independent_runtime.py','code/vendor/independent_runtime.py')]:
            need((ROOT/local).read_bytes()==z.read(pre+member),'Baseline binding: '+local)
    return{'selected_U212_bound':True,'unmodified_runtime_engines_bound':True}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--quick',action='store_true',help='explicitly skip fresh unbounded-runtime replay')
    p.add_argument('--report',type=Path,help='optional report outside the sealed release');a=p.parse_args()
    need(__debug__ and not sys.flags.optimize,'Use ordinary Python; local checker can separately run with -O')
    start=time.monotonic();count=hashes();bound=binding()
    import build,check_local,check_source_startup,compare
    with tempfile.TemporaryDirectory(prefix='u209-replay-')as temporary:
        temp=Path(temporary);built=build.build(temp/'machine')
        for name in['u209.tm','u209.native.tm','prefold212.native.tm','doublefold210.native.tm','sites.json','state_map.json','construction.json']:
            need((temp/'machine'/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),'Rebuild differs: '+name)
        local=check_local.check(temp/'machine',temp/'local.json')
        subprocess.run([sys.executable,'-B','-O',str(ROOT/'code/check_local.py'),'--machine',str(temp/'machine'),'--output',str(temp/'optimized.json')],check=True,stdout=subprocess.DEVNULL)
        need(json.loads((temp/'optimized.json').read_text())==json.loads(json.dumps(local)),
             'Optimized local checker differs')
        source=check_source_startup.check(temp/'machine',temp/'source_startup.json')
        compared=compare.check(temp/'comparison.json')
        runtime=None
        if not a.quick:
            from check_runtime import check
            runtime=check(temp/'machine',temp/'runtime',compare=True)
        result={'status':'U209_QUICK_PASS_RUNTIME_SKIPPED'if a.quick else'U209_FULL_REPLAY_PASS',
          'manifest_files':count,'working_states':209,'transition_rows':418,
          'native_sha256':built['sha256']['u209.native.tm'],'dense_sha256':built['sha256']['u209.tm'],
          'source_sha256':built['sha256']['sites.json'],'dependency_binding':bound,
          'local_cases':len(local['cases']),'engine_repair_cases':len(local['engine_repair_cases']),
          'negative_controls':len(local['negative_controls_rejected']),'ordinary_quotient_rows':local['ordinary_rows'],
          'source_primitives':source['primitives'],'control_edges':source['control_edges'],
          'prefix_interfaces':source['internal_prefixes'],'startup_steps':source['startup']['steps'],
          'incoming_comparison':compared['status'],'fresh_runtime_cases':runtime['cases']if runtime else 0,
          'literal_runtime_row_coverage':runtime['row_coverage']if runtime else 0,
          'symbolic_inferences':runtime['symbolic_inferences']if runtime else 0,
          'seconds':time.monotonic()-start,
          'scope':'New literal/source reduction checked by executable mathematical induction; inherited U/PA calibration retained. No new kernel-checked PA endpoint.'}
    need(hashes()==count,'Release changed during replay')
    if a.report:
        need(not a.report.resolve().is_relative_to(ROOT),'Place replay receipt outside sealed release');write_json(a.report,result)
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
