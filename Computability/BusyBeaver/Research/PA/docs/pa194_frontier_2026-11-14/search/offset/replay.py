#!/usr/bin/env python3
"""Replay bounded merger searches without modifying frozen evidence."""
from pathlib import Path
import argparse,json,re,subprocess,sys,tempfile
HERE=Path(__file__).resolve().parent
FAMILIES=('primary','four_l','ax11h','generalizer','ax11qh','ax11s','ax11g','gh')
def counters(s):
    m=re.search(r'pairs (\d+) trials (\d+) combos (\d+) hits (\d+)',s)
    if not m:raise ValueError('Missing completed search summary')
    return tuple(map(int,m.groups()))
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--family',choices=(*FAMILIES,'all'),default='all')
    ap.add_argument('--output',type=Path)
    ap.add_argument('--recorded-contexts',action='store_true',help='Reuse frozen source envelopes; normally regenerate them.')
    a=ap.parse_args();out=a.output or Path(tempfile.mkdtemp(prefix='pa-offset-'))
    out.mkdir(parents=True,exist_ok=True)
    if out.resolve()==HERE or HERE/'recorded' in out.resolve().parents:raise ValueError('Choose a fresh output directory')
    binary=out/'search'
    subprocess.run(['g++','-O3','-std=c++17',str(HERE/'search.cpp'),'-o',str(binary)],check=True)
    results={}
    for name in (FAMILIES if a.family=='all' else (a.family,)):
        inp=HERE/'inputs'/name;dest=out/name;dest.mkdir(exist_ok=True)
        contexts=HERE/'recorded'/name/'contexts_k6.tsv'
        if not a.recorded_contexts:
            contexts=dest/'contexts_k6.tsv'
            with (dest/'context_receipt.json').open('w') as log:
                subprocess.run([sys.executable,'-B',str(HERE/'collect_source_contexts.py'),str(inp/'machine.native.tm'),str(inp/'sites.json'),str(inp/'instructions.json'),str(contexts),'6'],check=True,stdout=log)
            assert contexts.read_bytes()==(HERE/'recorded'/name/'contexts_k6.tsv').read_bytes()
        rr={}
        for delta in (-2,0,2):
            r=subprocess.run([str(binary),str(inp/'machine.native.tm'),str(contexts),'6','160',str(delta)],text=True,capture_output=True,check=True)
            (dest/f'offset{delta}.jsonl').write_text(r.stdout)
            (dest/f'offset{delta}.log').write_text(r.stderr)
            old=HERE/'recorded'/name
            assert r.stdout==(old/f'offset{delta}.jsonl').read_text()
            assert counters(r.stderr)==counters((old/f'offset{delta}.log').read_text())
            rr[str(delta)]=dict(zip(('pairs','trials','combos','hits'),counters(r.stderr)))
        results[name]=rr
        print(name,'PASS',flush=True)
    (out/'receipt.json').write_text(json.dumps({'status':'PASS','families':results},indent=2)+'\n')
    print(out/'receipt.json')
if __name__=='__main__':main()
