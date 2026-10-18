#!/usr/bin/env python3
"""RePair on independently commuting canonical words; grammar evidence only."""
from pathlib import Path
from functools import lru_cache
import argparse,json,time
from grammar_search import attempt

ROOT=Path(__file__).resolve().parents[1]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--runs',type=int,default=5000);args=ap.parse_args()
    source=json.loads((ROOT/'search/decoder/closed-sequence-grammar.json').read_text())
    commuting=json.loads((ROOT/'search/grammar/results/commutation-analysis.json').read_text())
    strings=[commuting['canonical_words'][str(q)] for q in source['required_entry_roots']]
    atoms=sorted({x for w in strings for x in w});ids={x:i for i,x in enumerate(atoms)}
    words=[[ids[x]for x in w]for w in strings];best=None;began=time.monotonic()
    for seed in range(args.runs):
        mode=('left','right','balanced','random')[seed%4]
        n,rules,roots=attempt(words,seed,mode)
        if best is None or n<best['states']:
            best=dict(states=n,seed=seed,mode=mode,rules=rules,roots=roots,atoms=atoms)
            print('best',n,'seed',seed,flush=True)
    @lru_cache(None)
    def expand(q):
        if str(q)in best['rules']:
            a,b=best['rules'][str(q)];return expand(a)+expand(b)
        return(best['atoms'][q],)
    assert [list(expand(q))for q in best['roots']]==strings
    result=dict(status='GRAMMAR_ONLY_NOT_A_TM',runs=args.runs,seconds=time.monotonic()-began,entry_roots=source['required_entry_roots'],result=best)
    (ROOT/'results/commuting-repair-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print('DONE',result['seconds'],flush=True)

if __name__=='__main__':main()
