#!/usr/bin/env python3
"""Reproduce the finite discovery search; acceptance uses separate proofs."""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, time

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline',type=Path,required=True)
    ap.add_argument('--domains',type=Path,default=Path(__file__).resolve().parent/'discovery_domains5.txt')
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--cxx',default='g++')
    a=ap.parse_args();here=Path(__file__).resolve().parent;out=a.output_dir.resolve();out.mkdir(parents=True,exist_ok=True)
    baseline=a.baseline.resolve();domains=a.domains.resolve()
    assert hashlib.sha256(baseline.read_bytes()).hexdigest()=='547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f'
    sources=[here/'helper_two_rows.cpp',here/'helper_compensation.cpp']
    binary=out/'helper_expand5'
    compile_cmd=[a.cxx,'-std=c++17','-O3','-DRADIUS=5','-DRELAXED_HALT=1','-DEXPAND_RETAINED=1',str(sources[0]),'-o',str(binary)]
    subprocess.run(compile_cmd,check=True)
    run_cmd=[str(binary),str(baseline),'63','127'];env=os.environ.copy();env['SYNTH_DOMAINS']=str(domains)
    started=time.monotonic()
    with (out/'candidates.txt').open('w')as stdout,(out/'search.log').open('w')as stderr:
        subprocess.run(run_cmd,env=env,stdout=stdout,stderr=stderr,check=True)
    rows=(out/'candidates.txt').read_text().splitlines();assert len(rows)==3 and all(row.startswith('SOLUTION 169 80 ')for row in rows)
    receipt={'status':'DISCOVERY_REPRODUCED','scope':'Sampled finite context search only; not the acceptance proof.','compile':compile_cmd,'run':run_cmd,'SYNTH_DOMAINS':str(domains),'seconds':time.monotonic()-started,'files':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in [baseline,domains,*sources]},'candidates':rows,'final_counts':(out/'search.log').read_text().splitlines()[-1]}
    (out/'reproduction.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
