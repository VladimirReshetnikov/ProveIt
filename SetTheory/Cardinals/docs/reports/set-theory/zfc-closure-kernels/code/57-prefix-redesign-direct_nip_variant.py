#!/usr/bin/env python3
"""Reuse three unique old NIP states for a specialized cache==1 test."""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import mp_protocol_runtime as p
import native_protocol_variants as n


def main():
    table,_=p.generate();table['204',1]=(1,'R','113')
    niptest=('T',('D',5),('T',('T',('D',5),('B',1)),('H',)))
    nip=('T',niptest,('T',('N',166),('N',187)))
    nodes,root=n.patch_path({'1110100101':nip})
    table.update({('46',0):(0,'R','255'),('46',1):(1,'R','62'),
                  ('62',0):(0,'R','143'),('62',1):(1,'R','78'),
                  ('77',0):(0,'R','256'),('77',1):(1,'R','254'),
                  ('255',0):(0,'R','53'),('255',1):(1,'R','77'),
                  ('256',0):(0,'R','53'),('256',1):(0,'L','48')})
    p.a.sites=n.native_sites(nodes,root)
    result=dict(scope=__doc__,working_states=len(table)//2,
                affine=p.certify(table,p.guards()),blank_initialization_proved=False)
    out=HERE/'direct_nip';out.mkdir(exist_ok=True)
    data=p.a.encoded(table);result['table_sha256']=hashlib.sha256(data).hexdigest()
    if result['affine']['passed']:(out/'modified254.tm').write_bytes(data)
    (out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    (out/'modified-native-tree.json').write_text(json.dumps(dict(root=root,nodes=nodes),indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
