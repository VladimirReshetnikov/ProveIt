#!/usr/bin/env python3
"""Replay bounded PA194N6 state-reduction screens; standard library only."""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, tempfile

HERE=Path(__file__).resolve().parent
EXPECTED='63b6f604ee34ee119eb92ce3125021257204142854dec416c6b955f0560b975a'
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--collect',action='store_true');args=ap.parse_args()
    table=HERE/'inputs/n6.machine.native.tm';sites=HERE/'inputs/n6.sites.json'
    assert hashlib.sha256(table.read_bytes()).hexdigest()==EXPECTED
    cxx=shutil.which('c++')or shutil.which('g++')
    if not cxx:raise SystemExit('A C++17 compiler is required.')
    with tempfile.TemporaryDirectory(prefix='pa194n6-reduction-')as tmp:
        work=Path(tmp);patterns=HERE/'n6_contexts/patterns_k5.txt'
        if args.collect:
            subprocess.run(['python3','-B',str(HERE/'n6_physical/collect_contexts.py'),str(table),str(sites),'58320',str(work/'contexts')],check=True)
            patterns=work/'contexts/patterns_k5.txt'
            assert patterns.read_bytes()==(HERE/'n6_contexts/patterns_k5.txt').read_bytes()
        windows=patterns.read_text().splitlines()
        assert len(windows)==29282 and len({int(x.split()[0])for x in windows})==194
        results={}
        for name in ['action_merge_all','edge_bypass']:
            exe=work/name
            subprocess.run([cxx,'-O3','-std=c++17',str(HERE/'n6_physical'/f'{name}.cpp'),'-o',str(exe)],check=True)
            p=subprocess.run([str(exe),str(table),'5','300',str(patterns)],text=True,capture_output=True,check=True)
            assert not p.stdout.strip(),p.stdout
            results[name]={'candidate_count':0,'status':'completed'}
        print(json.dumps({'table_sha256':EXPECTED,'radius':5,'step_bound':300,'contexts':29282,'regenerated_contexts':args.collect,'results':results,'scope':'Unsuccessful finite local searches, not a machine-size lower bound.'},indent=2))

if __name__=='__main__':main()
