#!/usr/bin/env python3
"""Apply authenticated row recipes and canonicalize the two K216 tables."""
from pathlib import Path
import argparse, hashlib, json

ROOT=Path(__file__).resolve().parent.parent

def need(ok, message):
    if not ok: raise ValueError(message)

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def parse(p):
    table={}
    for lineno,line in enumerate(p.read_text().splitlines(),1):
        if not line or line.startswith('#'): continue
        parts=line.split()
        need(len(parts)==5, f'Bad row at {p}:{lineno}')
        q,b,w,d,z=parts
        q,b,w,z=map(int,(q,b,w,z))
        need(b in (0,1) and w in (0,1) and d in ('L','R'), 'Bad alphabet or movement')
        need((q,b) not in table, 'Duplicate transition')
        table[q,b]=(w,d,z)
    return table

def build(base, permutation, output):
    recipe=json.loads((ROOT/f'provenance/transition_recipe{permutation}.json').read_text())
    need(sha(base)==recipe['baseline_sha256'], 'K217 table input hash')
    table=parse(base)
    keys=set()
    for row in recipe['rows']:
        key=row['state'],row['read']
        need(key not in keys,'Duplicate recipe key'); keys.add(key)
        before=tuple(row['old']) if row['old'] is not None else None
        need(table.get(key)==before,f'Recipe precondition at {key}')
        if row['new'] is None: del table[key]
        else: table[key]=tuple(row['new'])
    states={q for q,b in table}
    need(len(states)==216 and len(table)==432,'216 states / 432 transitions')
    need(all((q,b) in table for q in states for b in (0,1)), 'Total working table')
    need(0 in states and 254 not in states,'Start / halt convention')
    need({z for w,d,z in table.values()}-states=={254}, 'Unique external halt')
    oldstates={q for q,b in parse(base)}
    need(sorted(oldstates-states)==recipe['deleted_states'],'Deleted state census')
    need(states<=oldstates and recipe['added_states']==[],'No state added')
    need(recipe['changed_retained_rows']==38,'38 retained rows changed')
    raw=('#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n'
         for (q,b),(w,d,z) in sorted(table.items()))).encode('ascii')
    need(hashlib.sha256(raw).hexdigest()==recipe['candidate_sha256'],'Native output hash')
    native=output/f'k216-{permutation}.native.tm';native.write_bytes(raw)
    mapping={q:i for i,q in enumerate(sorted(states))};mapping[254]=216
    compact=('#! start 0\n#! halt 216\n'+''.join(
        f'{mapping[q]} {b} {w} {d} {mapping[z]}\n'
        for (q,b),(w,d,z) in sorted(table.items()))).encode('ascii')
    canonical=output/f'k216-{permutation}.tm';canonical.write_bytes(compact)
    # A direct inverse check, separate from the serialization format.
    inv={v:k for k,v in mapping.items()}
    renamed=parse(canonical)
    need({(inv[q],b):(w,d,inv[z]) for (q,b),(w,d,z) in renamed.items()}==table,
         'Canonicalization is a bijection on the literal table')
    return {'permutation':permutation,'native_sha256':sha(native),
            'canonical_sha256':sha(canonical),'working_states':216,'rows':432,
            'deleted_states':recipe['deleted_states'],'changed_retained_rows':38}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline217',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    result={'status':'PASS_EXACT_TABLE_RECONSTRUCTION',
            'machines':[build(a.baseline217,p,a.output) for p in ('210','120')]}
    (a.output/'reconstruction.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
