#!/usr/bin/env python3
"""Replay optional, explicitly selected finite reduction experiments.

No search runs implicitly as part of machine verification. Binaries are
compiled in a temporary directory, not the supplied packet. Every output
goes to the directory selected with --output.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def run(args,stdout=None,stderr=None):
    if stdout:
        with stdout.open('w') as out:
            if stderr:
                with stderr.open('w') as err:
                    subprocess.run(list(map(str,args)),check=True,stdout=out,stderr=err)
            else:
                subprocess.run(list(map(str,args)),check=True,stdout=out)
    else:
        subprocess.run(list(map(str,args)),check=True)

def merge_counts(path):
    text=path.read_text()
    m=re.search(r'DONE pairs (\d+) trials (\d+) combos (\d+) hits (\d+) seconds ',text)
    if not m:raise RuntimeError('Missing completed search receipt')
    return dict(zip(('pairs','trials','combos','hits'),map(int,m.groups())))

def require(cond,message):
    if not cond:raise RuntimeError(message)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--suite',choices=['radius4','radius6','heuristic','tail','all'],required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    require(sys.flags.optimize==0,'Run without -O or PYTHONOPTIMIZE: the inherited symbolic checker uses assertions.')
    out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
    require(out!=ROOT,'Choose a separate output directory')
    suites=['radius4','radius6','heuristic','tail'] if a.suite=='all' else [a.suite]
    result={'suites':{}}
    table=ROOT/'inputs/pa194B.native.tm'
    require(sha(table)=='f9d8b134f99b669d2339b92e062100d5ad854874a23bd8f8aa1141821667d08e','Pinned PA194B input mismatch')
    def contexts(k):
        path=out/f'contexts{k}.txt'
        if not path.exists():
            run([sys.executable,'-B',ROOT/'src/collect_source_contexts.py',table,
                 ROOT/'inputs/primary.sites.json',ROOT/'inputs/primary.instructions.json',
                 path,k],out/f'contexts{k}_receipt.json')
        require(sha(path)==sha(ROOT/f'recorded/contexts{k}.txt'),f'Radius{k} source contexts differ')
        return path
    with tempfile.TemporaryDirectory(prefix='pa194b-optional-search-') as temporary:
        tmp=Path(temporary)
        merger=tmp/'joint_return_merge'
        if any(s!='tail' for s in suites):
            run([os.environ.get('CXX','g++'),'-std=c++17','-O3',ROOT/'src/joint_return_merge.cpp','-o',merger])
        for suite in suites:
            print('Running',suite,flush=True)
            if suite in ('radius4','radius6'):
                k=int(suite[-1]);ctx=contexts(k)
                log=out/f'merge_search{k}.log';hits=out/f'merge_hits{k}.jsonl'
                run([merger,table,k,100,ctx],hits,log)
                counts=merge_counts(log)
                require(counts==merge_counts(ROOT/f'recorded/merge_search{k}.log'),'Search counters differ')
                require(hits.read_bytes()==(ROOT/f'recorded/merge_hits{k}.jsonl').read_bytes(),'Search hit set differs')
                result['suites'][suite]={'radius':k,'step_bound':100,**counts,'context_sha256':sha(ctx)}
            elif suite=='heuristic':
                collector=tmp/'sample_boxes'
                run([os.environ.get('CXX','g++'),'-std=c++17','-O3',ROOT/'src/sample_boxes.cpp','-o',collector])
                box=out/'box_samples4.txt'
                run([collector,table,ROOT/'inputs/sample_sites.txt',4],box,out/'box_samples4.log')
                require(sha(box)==sha(ROOT/'recorded/box_samples4.txt'),'Sampled engine contexts differ')
                ctx=out/'context_samples4.txt'
                ctx.write_bytes(contexts(4).read_bytes()+box.read_bytes())
                log=out/'sample_merge.log';hits=out/'sample_merge_hits.jsonl'
                run([merger,table,4,100,ctx],hits,log)
                counts=merge_counts(log)
                require(counts==merge_counts(ROOT/'recorded/sample_merge.log'),'Heuristic search counters differ')
                require(hits.read_bytes()==(ROOT/'recorded/sample_merge_hits.jsonl').read_bytes(),'Heuristic hit set differs')
                result['suites'][suite]={'radius':4,'step_bound':100,**counts,'engine_context_sha256':sha(box),
                                        'scope':'Heuristic candidate search; sampled engine windows are not a universal correctness certificate.'}
            else:
                target=out/'tail_search.json'
                run([sys.executable,'-B',ROOT/'src/tail_search.py','--steps',100,'--head-limit',100,'--output',target],out/'tail_stdout.json')
                fresh=json.loads(target.read_text())
                recorded=json.loads((ROOT/'recorded/tail_search.json').read_text())
                for k in ('tested','classification','hits'):
                    require(fresh[k]==recorded[k],f'Tail-search {k} differs')
                result['suites'][suite]={'tested':fresh['tested'],'classification':fresh['classification'],
                    'successful_actions':len(fresh['hits']),'steps_bound':100,'right_head_limit':100}
            print('Matched recorded result:',suite,flush=True)
    result['scope']='Finite search replays only. No global lower bound; no sub194 claim.'
    (out/'replay_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
