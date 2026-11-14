#!/usr/bin/env python3
"""Replay the frozen, bounded common-future physical fold screens.

This is a heuristic proposal screen, not a theorem that no smaller machine
exists. A positive result would still require a complete source-frame proof,
literal arithmetic-box verification and a calibrated blank startup.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, tempfile

ROOT=Path(__file__).resolve().parent

def metadata(path):
    tokens=iter(map(int,path.read_text().split()))
    radius=next(tokens);nrows=next(tokens)
    for _ in range(5*nrows):next(tokens)
    count=next(tokens);contexts=0
    for _ in range(count):
        q=next(tokens);n=next(tokens);contexts+=n
        for _ in range(n):next(tokens)
    assert next(tokens,None) is None
    return {'radius':radius,'working_states':nrows//2,
            'eligible_controls':count,'control_pairs':count*(count-1)//2,
            'context_instances':contexts,
            'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}

def main():
    if not __debug__:
        raise SystemExit('Run this replay with Python assertions enabled (do not use -O).')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result={'status':'PASS','scope':'Bounded heuristic local-fold search; no global lower bound.',
            'maximum_literal_steps':32,'scanned_offsets':[-4,4],
            'merged_control_reentry':'Both rows coupled; reentry allowed.',
            'candidate_first_actions':'Any write bit, either direction, any surviving control or halt.',
            'rendezvous':'Any positive old trajectory prefix within the same window and step bound.',
            'searches':[]}
    with tempfile.TemporaryDirectory(prefix='pa-physical-search-') as temporary:
        binary=Path(temporary)/'coupled_search'
        subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'coupled_search.cpp'),'-o',str(binary)],check=True)
        for filename in ['primary_contexts.txt','4l_contexts.txt','4l_literal_r4.txt','ax11g_contexts.txt']:
            path=ROOT/filename
            if not path.is_file():
                raise FileNotFoundError(f'Required frozen search input is missing: {path}')
            completed=subprocess.run([str(binary),str(path),'future'],text=True,capture_output=True,check=True)
            stats=metadata(path);stats['input']=filename
            stats['candidates']=len(completed.stdout.splitlines())
            stats['stderr']=completed.stderr.strip()
            assert stats['candidates']==0,completed.stdout
            assert completed.stderr.strip()==f"pairs {stats['control_pairs']} candidates 0"
            result['searches'].append(stats)
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
