"""Fast exact data audit; full pricing reruns are separate reproducible commands."""
from pathlib import Path
from functools import cache
import json,hashlib
HERE=Path(__file__).resolve().parent

def dag_score(j):
    s=j['structures']
    @cache
    def go(n):
        x=s[n]
        if isinstance(x[0],str):return frozenset([n]),0,0,0,1
        a,b=map(go,x)
        return a[0]|b[0]|{n},1+a[1],max(1+a[1],a[2],b[2]),1+max(a[3],b[3]),a[4]+b[4]
    live,lead,zero,depth,leaves=go(j['root'])
    return [len(live),zero,depth],leaves

def main():
    base=json.loads((HERE/'boundary_source_input.json').read_text());assert dag_score(base)==([224,6,48],6455)
    nip=json.loads((HERE/'nip_source.json').read_text());assert dag_score(nip)==([224,6,48],6449)
    results=[]
    for basis,cases in [('ksp',288),('ksq4',288),('ksqdn',288),('ksdne',288),('bundle',64)]:
        receipt=json.loads((HERE/'receipts'/f'{basis}.json').read_text())
        best=json.loads((HERE/'best_sources'/f'{basis}.json').read_text())
        assert receipt['cases']==len(receipt['rows'])==cases
        metric=min(r['score']for r in receipt['rows'])
        assert metric==receipt['best']==best['score']==dag_score(best)[0]
        assert best['expanded_source_leaves']==dag_score(best)[1]
        assert metric[1]<=6 and best['status']=='SOURCE_COST_ONLY_UNCOMPILED'
        results.append(dict(basis=basis,cases=cases,best=metric))
    contracts=json.loads((HERE/'macro_contract_receipt.json').read_text())
    assert contracts['status']=='PASS'and contracts['macros']==19
    assert contracts['product_pairs']==192 and contracts['decrement_edges']==346
    assert sum(len(row['transfer_rotation_lemmas'])for row in contracts['rows'])==1
    if(HERE/'MANIFEST.json').exists():
        files=json.loads((HERE/'MANIFEST.json').read_text())['sha256']
        for name,want in files.items():assert hashlib.sha256((HERE/name).read_bytes()).hexdigest()==want,name
    print(json.dumps(dict(status='PASS',baseline=[224,6,48],results=results)))

if __name__=='__main__':main()
