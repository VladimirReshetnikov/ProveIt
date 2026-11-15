#!/usr/bin/env python3
"""Exact tuple comparison against every frozen spanning 194-state reference."""
from pathlib import Path
import argparse,hashlib,json
import novelty_helpers as nh

ROOT=Path(__file__).resolve().parents[1]

def serial(obj):return json.dumps(obj,separators=(',',':'))
def sha(obj):return hashlib.sha256(serial(obj).encode()).hexdigest()

def check(machine_root=ROOT/'machines',recompute=False,output=None):
    cache=ROOT/'comparison/reference_194_strong.json'
    refs=json.loads(cache.read_text())
    assert len(refs)==548
    if recompute:
        for r in refs:
            rows,states,start=nh.parse((ROOT/'comparison/tables194'/(r['key']+'.tm')).read_bytes())
            assert serial(nh.canonical(rows,states))==serial(r['canonical'])
            assert serial(nh.strong(rows,states))==serial(r['strong'])
    known={serial(r['strong'])for r in refs}
    results=[];peers=set()
    for name in ('PA194ForestR','PA194ForestB','PA194ForestX'):
        path=machine_root/name/'machine.tm'
        rows,states,start=nh.parse(path.read_bytes())
        assert len(states)==nh.reachable(rows,states,start)==194
        identity=nh.strong(rows,states);key=serial(identity)
        assert key not in known and key not in peers
        peers.add(key)
        results.append({'name':name,'states':194,'start':start,
                        'dense_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
                        'strong_class_sha256':sha(identity),'new_vs_all_references':True,
                        'ordinary_bisimulation_states':nh.bisimulation_count(rows,states)})
    out={'status':'PASS','reference_classes':548,'candidates':results,
         'equivalences_excluded':'arbitrary spanning roots, state renaming, reflection, global symbol exchange, ignored halt actions',
         'method':'exact canonical tuple equality; digests identify the resulting tuples',
         'recomputed_reference_canonical_forms':recompute}
    (output or ROOT/'comparison/final_novelty.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2));return out

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--machines',type=Path,default=ROOT/'machines')
    parser.add_argument('--recompute',action='store_true')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args();check(args.machines,args.recompute,args.output)
