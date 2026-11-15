#!/usr/bin/env python3
"""Recompute exact state-renaming classes and verify pinned catalog coverage.

Run from any working directory. Every one of the catalogued 528 complete
194-state classes and 55 complete 193-state classes must be represented. The
extra incoming classes are identified separately from named proposals.
"""
from pathlib import Path
import argparse,csv,collections,hashlib,json
from census import parse_text,canon,COMMIT

HERE=Path(__file__).resolve().parent

def cls(table):
    roots=[canon(table,q) for q in table[1]]
    spanning=[h for h,n in roots if n==len(table[1])]
    return min(spanning) if spanning else None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,default=HERE/'coverage.json');ap.add_argument('--cache',type=Path)
    a=ap.parse_args()
    cache=json.loads(a.cache.read_text()) if a.cache and a.cache.exists() else {}
    catalog=list(csv.DictReader((HERE/'upstream_MACHINES.tsv').open(),delimiter='\t'))
    old={n:{r['table_class'] for r in catalog if int(r['states'])==n} for n in (193,194)}
    names=json.loads((HERE/'named_designs104.json').read_text())['designs'];by_named={r['table_class']:r['name'] for r in names}
    idx={r['file']:r for r in json.loads((HERE/'corpus_index.json').read_text())['records']}
    rows=[]
    for n in (193,194):
        for j,p in enumerate(sorted((HERE/('corpus'+str(n))).glob('*.tm'))):
            data=p.read_bytes();raw=hashlib.sha256(data).hexdigest();t=parse_text(data)
            assert t and len(t[1])==n
            cached=cache.get(raw)
            if cached and cached['states']==n:
                h=cached['table_class']
            else:
                h=cls(t)
            if n==193:assert h==p.stem,(p,h)
            rows.append({'file':str(p.relative_to(HERE)),'states':n,'raw_sha256':raw,'table_class':h,'in_filed_catalog':h in old[n],
                         'named_design':by_named.get(h,''),'original_path':idx.get(p.name,{}).get('original_path','retained MF audit193 corpus')})
            if j%100==0:print(n,j,flush=True)
    actual={n:{r['table_class'] for r in rows if r['states']==n and r['table_class']} for n in (193,194)}
    missing={str(n):sorted(old[n]-actual[n]) for n in (193,194)}
    assert not any(missing.values()),missing
    assert len(actual[193])==55 and len(actual[194])==548
    assert set(by_named)<=actual[194]
    result={'commit':COMMIT,'catalog_classes193':len(old[193]),'catalog_classes194':len(old[194]),
        'covered_catalog193':len(old[193]&actual[193]),'covered_catalog194':len(old[194]&actual[194]),'missing_catalog_classes':missing,
        'complete_spanning_classes193':len(actual[193]),'complete_spanning_classes194':len(actual[194]),
        'named_positive_claim_classes194':len(by_named),'named_classes_missing':sorted(set(by_named)-actual[194]),
        'additional_194_classes':sorted(actual[194]-old[194]),
        'unnamed_additional_194_classes':sorted(actual[194]-old[194]-set(by_named)),
        'nonspanning194_byte_forms':sum(r['states']==194 and r['table_class'] is None for r in rows),
        'tables':rows}
    a.out.write_text(json.dumps(result,indent=2)+'\n')
    with (a.out.parent/'class_catalog.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)
    print(json.dumps({k:v for k,v in result.items() if k!='tables'},indent=2))

if __name__=='__main__':main()
