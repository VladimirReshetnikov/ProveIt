#!/usr/bin/env python3
"""Direct 254-state implementation of AX's shifted-GEN protocol variant."""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import mp_protocol_runtime as p


def main():
    table,nodes=p.generate()
    table['204',1]=(1,'R','113')
    # Original-prefix context:76 ->86 ->98 ->113. States86 and98 are shared
    # elsewhere, so copy exactly two of them. 76 has a single code use.
    assert table['76',0]==(0,'R','86')
    table['76',0]=(0,'R','255')
    table['255',0]=(0,'R','256');table['255',1]=table['86',1]
    table['256',0]=(0,'R','132');table['256',1]=table['98',1]
    oldraw=(p.audit.ROOT/'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v').read_text()
    nodes=p.tree(oldraw)
    prefix='111010010010000'
    outer,inner=p.subtree(nodes,prefix),p.subtree(nodes,prefix+'1')
    nodes[outer]=nodes[inner]
    p.a.sites=p.sites(nodes)
    out=HERE/'direct_ax';out.mkdir(exist_ok=True)
    result=dict(scope=__doc__,working_states=len(table)//2,
                cases=sum(2 if op=='CD' else 1 for _,op,_ in p.a.sites),
                affine=p.certify(table,p.guards()),
                blank_initialization_proved=False)
    assert result['affine']['passed']
    data=p.a.encoded(table)
    result['table_sha256']=hashlib.sha256(data).hexdigest()
    (out/'modified254.tm').write_bytes(data)
    (out/'modified-tree.json').write_text(json.dumps(nodes,indent=2)+'\n')
    (out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
