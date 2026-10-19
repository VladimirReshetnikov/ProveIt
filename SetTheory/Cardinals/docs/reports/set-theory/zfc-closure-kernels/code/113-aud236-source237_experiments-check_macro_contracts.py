"""Replay Source91's bisimulation method for the exact current source atoms.

The checker and independent path semantics are explicitly attributed copies;
this adapter changes only parsing of the pinned .node-format Lean data and
selection of the precise current source-DAG atom expansions.
"""
import json,re,hashlib
from pathlib import Path
from functools import cache
import pricing as p
import macro_contracts as c
import rmpath
HERE=Path(__file__).resolve().parent

def original_dag():
    nodes={}
    for line in (HERE/'Dag254.lean').read_text().splitlines():
        m=re.match(r'\s*\|\s*(\d+)\s*=>\s*(.*?)(?:\s*--.*)?$',line)
        if not m:continue
        edges=re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?:\s+(\d+))?',m[2])
        assert len(edges)==2
        nodes[int(m[1])]=edges
    assert set(nodes)==set(range(219))
    @cache
    def edge(op,n):
        if op=='node':return ('N',*(edge(*v)for v in nodes[int(n)]))
        return ('L',('dec'if op=='decnz'else op,int(n)))if n else ('L',(op,))
    return lambda n:edge('node',str(n))

@cache
def current(n):
    x=p.e.S[n]
    if isinstance(x[0],int):return ('N',current(x[0]),current(x[1]))
    op={'CI':'inc','CD':'dec','CB':'brk','CC':'cont','CH':'halt'}[x[0]]
    return ('L',(op,x[1]))if op!='halt'else ('L',(op,))

def normalize_rotated_transfer(tree,rewrites):
    if tree[0]=='L':return tree
    a,b=tree[1:]
    if (a[0]=='L'and a[1][0]=='inc'and b[0]=='N'
        and b[1][0]=='L'and b[1][1][0]=='dec'
        and b[2]==('L',('cont',2))and a[1][1]!=b[1][1][1]):
        # With X initially n, both sides clear X and increment distinct Y by
        # n+1. Induction on n proves finite termination and exact equality.
        # [Y++; while (--X) loop] -> [while (--X) Y++; Y++]
        rewrites.append(dict(increment=a[1][1],counter=b[1][1][1]))
        return ('N',('N',b[1],('N',a,b[2])),a)
    return ('N',normalize_rotated_transfer(a,rewrites),normalize_rotated_transfer(b,rewrites))

def main():
    old=original_dag();rows=[];certs={}
    for m,w in sorted(p.M.items()):
        rewrites=[]
        target=normalize_rotated_transfer(c.sequence([current(n)for n in w]),rewrites)
        left=c.Graph(old(m));right=c.Graph(target)
        cert=c.make_certificate(left,right)
        c.check_with_upstream(left,right,cert,rmpath)
        certs[str(m)]=cert
        rows.append(dict(macro=m,product_pairs=len(cert['vertices']),
            decrement_edges=2*sum(v['operation'][0]=='dec'for v in cert['vertices']),
            original_leaves=len(left.leaves)-1,current_leaves=sum(len(c.leaves(current(n)))for n in w),
            normalized_leaves=len(right.leaves)-1,transfer_rotation_lemmas=rewrites))
    out=dict(status='PASS',scope='All-nine-register equality of each closed macro partial function; both guard outcomes and return/divergence preserved',
        macros=len(rows),product_pairs=sum(r['product_pairs']for r in rows),
        decrement_edges=sum(r['decrement_edges']for r in rows),rows=rows)
    (HERE/'macro_contract_receipt.json').write_text(json.dumps(out,indent=2)+'\n')
    (HERE/'macro_contract_certificates.json').write_text(json.dumps(certs,indent=2)+'\n')
    print(json.dumps(out))

if __name__=='__main__':main()
