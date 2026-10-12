"""Deterministic correctness/capacity audit. Run from the package root."""
import argparse
from collections import Counter
from hashlib import sha256
import itertools
import json
from pathlib import Path
import platform
import random
import sys
from time import perf_counter
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot.compressed_braid import Builder, recognize, verify
from fastunknot.compressed_braid.engine import recognize as raw_recognize
from fastunknot.compressed_braid.verify import verify as raw_verify
from fastunknot.braid import braid_certificate
from fastunknot.diagram import DiagramError
from fastunknot.compressed_braid.engine import normal_form
from fastunknot.compressed_braid.grammar import expand, validate
from fastunknot.compressed_words import WordArena as Arena
recognize_forest, verify_forest = recognize, verify
from compressed_braid_research.oracles import explicit, matrix, cyclic_tokens
from compressed_braid_research.families import sleeve, singleton_forest


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--max-length', type=int, default=8)
    p.add_argument('--output', type=Path, default=ROOT/'results/audit.json')
    args=p.parse_args()
    started=perf_counter()
    counts=Counter()
    for n in range(args.max_length+1):
        print("starting length",n,flush=True)
        for word in itertools.product((1,-1,2,-2),repeat=n):
            b=Builder(); data=b.data(b.word(word))
            out=raw_recognize(data)
            try: expected=braid_certificate(3,word)['status']
            except DiagramError: expected='LINK'
            assert out['status']==explicit(word)==matrix(word)==expected
            assert raw_verify(data,out['certificate'])==out['status']
            counts[out['status']]+=1
    print("exhaustive complete",dict(counts),flush=True)
    rng=random.Random(20261008)
    random_cases=400
    quotient_cases=0
    for _ in range(random_cases):
        b=Builder()
        roots=[b.word([rng.choice((1,-1,2,-2))]) for j in range(4)]
        for j in range(14):
            u,v=rng.choices(roots,k=2)
            if rng.randrange(3)==0:
                u=b.inverse(u)
            roots.append(b.concat(u,v))
        data=b.data(roots[-1]); word=expand(data,limit=100000)
        out=recognize(data)
        assert out['status']==explicit(word)==matrix(word)
        assert verify(data,out['certificate'])==out['status']
        _,arena,proof=normal_form(data, equality_probe_steps=0, prefix_probe_steps=0)
        core=arena.expand(proof[2],limit=300000)
        image={1:(3,1),-1:(1,2),2:(1,3),-2:(2,1)}
        wanted=cyclic_tokens([t for g in word for t in image[g]])
        # The cyclic normal forms may differ by rotation.
        assert len(core)==len(wanted)
        assert not core or any(core==wanted[j:]+wanted[:j] for j in range(len(core)))
        quotient_cases+=1
    print("random complete",flush=True)
    capacity=[]
    for k in (64,256,1024,4096):
        for negative in ((False,True) if k <= 256 else (False,)):
            print("capacity",k,negative,flush=True)
            data=sleeve(k,negative=negative)
            with patch.object(Arena,'expand',side_effect=AssertionError('expansion forbidden')):
                begin=perf_counter(); out=recognize(data); discovery=perf_counter()-begin
                begin=perf_counter(); verdict=verify(data,out['certificate']); replay=perf_counter()-begin
            assert verdict==('KNOTTED' if negative else 'UNKNOT')
            capacity.append(dict(k=k,negative=negative,expanded_length_hex=hex(validate(data).lengths[data['root']]),
                input_rules=len(data['rules'])-1,stats=out['stats'],
                certificate_bytes=len(json.dumps(out['certificate'],separators=(',',':')).encode()),
                discovery_seconds=discovery,verification_seconds=replay,status=verdict))
    print("capacity complete",flush=True)
    reassociated=[]
    for k in (4,8,16,32):
        print("reassociated",k,flush=True)
        data=sleeve(k,reassociated=True)
        begin=perf_counter()
        out=recognize(data,equality_probe_steps=0,prefix_probe_steps=0)
        assert verify(data,out['certificate'],equality_probe_steps=0,prefix_probe_steps=0)=='UNKNOT'
        reassociated.append(dict(k=k,stats=out['stats'],seconds=perf_counter()-begin))
    print("reassociated complete",flush=True)
    forests=[]
    for factors,k,negative in ((4,16,None),(16,128,None),(16,128,7),(32,256,None)):
        print("forest",factors,k,negative,flush=True)
        data=singleton_forest(factors,k,negative_index=negative)
        with patch.object(Arena,'expand',side_effect=AssertionError('expansion forbidden')):
            begin=perf_counter(); out=recognize_forest(data); discovery=perf_counter()-begin
            begin=perf_counter(); verdict=verify_forest(data,out['certificate']); replay=perf_counter()-begin
        assert verdict==('UNKNOT' if negative is None else 'KNOTTED')
        forests.append(dict(factors=factors,k=k,negative_index=negative,strands=data['strands'],
            input_rules=len(data['rules'])-1,status=verdict,discovery_seconds=discovery,
            verification_seconds=replay,certificate_bytes=len(json.dumps(out['certificate']).encode())))
    result=dict(python=sys.version,platform=platform.platform(),seed=20261008,
                scope='Maintained explicit braid gateway and exact Burau controls; exhaustive low-level replay, public shared-budget host on random/capacity/forest cases.',
                exhaustive_max_length=args.max_length,exhaustive_cases=sum(counts.values()),
                exhaustive_counts=dict(counts),random_grammar_cases=random_cases,
                forced_fallback_quotient_cases=quotient_cases,capacity=capacity,
                reassociated=reassociated,forests=forests,elapsed_seconds=perf_counter()-started,
                source_sha256={str(x.relative_to(ROOT)):sha256(x.read_bytes()).hexdigest()
                    for x in sorted((ROOT/'fastunknot/compressed_braid').glob('*.py')) + [ROOT/'fastunknot/compressed_words.py',ROOT/'fastunknot/braid.py',Path(__file__).resolve(),ROOT/'compressed_braid_research/families.py',ROOT/'compressed_braid_research/oracles.py']})
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('source_sha256','capacity','reassociated','forests')},indent=2))
    print('Capacity:',[(r['k'],r['negative'],r['stats']['arena_nodes']) for r in capacity])

if __name__=='__main__':main()
