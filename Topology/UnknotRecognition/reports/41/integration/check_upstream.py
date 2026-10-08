#!/usr/bin/env python3
"""Optional source-pinned gateway. NOT executed in the delivered environment.

Run with a complete ProveIt checkout. This tests the real WordArena bridge and
legacy replay, not full recognizer integration or end-to-end performance.
"""
import argparse,hashlib,json,random,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
PIN='81a387aada56bb180649a98c21c078cb89efcfde'
BLOBS={'compressed_words.py':'bd68418e226813a7fa50dc87405c214970ddf50e',
       'whitehead_power.py':'d235def0cf042e9e6407c89512b023127d811ec4',
       'compressed_search.py':'ff33437267d37bc874b00cb4e087f083b94e1a7b',
       'group_certificate.py':'922510eda5b7e6731de43e639c7dafcb47a56361'}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--fast-root',type=Path,required=True,help='.../Topology/UnknotRecognition/fast')
    ap.add_argument('--allow-unpinned',action='store_true')
    ap.add_argument('--output',type=Path)
    a=ap.parse_args(); hashes={}
    for name,expected in BLOBS.items():
        data=(a.fast_root/'fastunknot'/name).read_bytes()
        found=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        hashes[name]={'expected':expected,'actual':found,'matches':expected==found}
    if not all(x['matches'] for x in hashes.values()) and not a.allow_unpinned:
        raise RuntimeError('source blobs differ from pin; inspect differences before --allow-unpinned')
    sys.path.insert(0,str(a.fast_root.resolve()))
    from fastunknot.compressed_words import WordArena
    from fastunknot.whitehead_power import power_profile
    from shear_kernel.adapter import import_arena,prepare_step,replay_in_arena
    from shear_kernel.histogram import profile
    from shear_kernel.reference import cyclic_reduce,canonical,first_line_minimum
    rng=random.Random(77317); comparisons=0
    for case in range(40):
        arena=WordArena(max_nodes=200000,max_work=50000000)
        words=[cyclic_reduce([rng.choice([1,-1,2,-2,3,-3]) for _ in range(14)]) for _ in range(3)]
        roots=[arena.from_word(w) for w in words]
        result,moves=prepare_step(arena,roots,{1,2,3})
        new,legacy=replay_in_arena(arena,roots,{1,2,3},result)
        assert legacy==moves
        for old,fresh in zip(new,result.roots):
            assert canonical(arena.expand(old,limit=100000))==canonical(result.grammar.expand(fresh))
            comparisons+=1
        g,rs=import_arena(arena,roots)
        multiplier=rng.choice([1,-1,2,-2,3,-3])
        subset={multiplier}|{v for v in [1,-1,2,-2,3,-3]
                            if abs(v)!=abs(multiplier) and rng.randrange(2)}
        p=profile(g,rs,multiplier); labels={v:int(v in subset) for pair in p.gaps for v in pair[:2]}
        exponent=first_line_minimum(p,labels)
        expected=(exponent,p.value({v:exponent*x for v,x in labels.items()})-p.original_length,
                  p.value(labels)-p.original_length)
        assert power_profile(arena,roots,multiplier,subset)==expected
        comparisons+=1
    report={'pin':PIN,'source_hashes':hashes,'comparisons':comparisons,'status':'passed',
            'scope':'WordArena/legacy move gateway only, not the production recognizer suite'}
    if a.output: a.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__': main()
