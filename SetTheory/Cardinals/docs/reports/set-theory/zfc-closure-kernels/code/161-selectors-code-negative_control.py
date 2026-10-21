#!/usr/bin/env python3
"""A released unbounded case passes; an inappropriate contextual CB entry fails."""
from pathlib import Path
import argparse,hashlib,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'runtime'))
import symbolic_runtime as rt

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--sites',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args()
    T=rt.r.table(a.table);sites=json.loads(a.sites.read_text())
    index=4697;site=sites[index]
    assert site==['11010011','CB',1] and T[135,1]==(0,-1,302)
    m={int(k):int(v) for k,v in json.loads((ROOT/'inputs/legacy_mapping.json').read_text()).items()}
    for q in {q for q,b in T}|{254}:
        if q not in m:m[q]=q+1000
    states={q for q,b in T}|{254}
    assert len({m[q] for q in states})==len(states) and m[84]==96 and m[254]==254
    L={(m[q],b):(w,d,m[z]) for (q,b),(w,d,z) in T.items()}
    lemmas,_=rt.prove_blocks(L);rt.case(L,lemmas,site,False)
    bad=dict(L);bad[m[135],1]=(0,-1,m[10])
    try:
        badlemmas,_=rt.prove_blocks(bad)
        rt.case(bad,badlemmas,site,False)
    except Exception as e:failure=repr(e)
    else:raise ValueError('The negative mutation was accepted')
    out={'status':'PASS_MUTATION_REJECTED',
         'table_sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),
         'site_index':index,'site':site,'baseline_case':'PASS',
         'old_native_row':[135,1,0,-1,302],'bad_native_row':[135,1,0,-1,10],
         'failure':failure,'scope':'One unbounded case, with block lemmas regenerated for each table. A negative control is not a proof of overall checker soundness.'}
    a.out.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
