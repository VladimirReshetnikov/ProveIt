#!/usr/bin/env python3
"""Produce the full q-cube-normalized positive graph from the sealed89 parent."""
import argparse,json,sys
from collections import Counter
from copy import deepcopy
from hashlib import sha256
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
PARENT=ROOT/'research/ten-positive-uncentered-b-weight'
SEAL='e4fe2d2e3d502619cfda003341fd08b49efea408ccdd569d3a551c64dd8f7ac0'
def need(ok,why):
    if not ok:raise ValueError(why)
def digest(p):return sha256(p.read_bytes()).hexdigest()
def encode(d):return (json.dumps(d,indent=2,sort_keys=True)+'\n').encode()
def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    pins=json.loads((HERE/'SOURCE_PINS.json').read_bytes())
    need(digest(PARENT/'MANIFEST.json')==SEAL,'exact whole calibrated89 parent')
    for n,h in pins['files'].items():need(digest(ROOT/n)==h,'whole frozen dependency '+n)
    old=json.loads((PARENT/'zero89.json').read_bytes());defs={r[0]:r for r in old['source']}
    deleted={'P1','qm1Y','q3Bt','inner'};moved={'q2','q3'}
    replacements={'P1mu2':['P1mu2','*','bJ','mu2'],'mu2inner':['mu2inner','*','mu2','Bt'],'P1e':['P1e','*','bJ','e'],'brk':['brk','+','mu2inner','P1e'],'Znum':['Znum','-','Zpart1','Zpart2']}
    rows=[]
    for row in old['source']:
        if row[0] in deleted|moved:continue
        rows.append(replacements.get(row[0],row))
        if row[0]=='q':rows += [defs['q2'],defs['q3'],['Y','*','q3','s']]
    packet=deepcopy(old);packet['witnesses']=['s' if v=='Y' else v for v in old['witnesses']]
    packet.update(name='qcube_normalized_zero86',source=rows,operations=len(rows),operation_breakdown=dict(Counter(r[1] for r in rows)),exact_degree=466,parent_sha256=digest(PARENT/'zero89.json'),parent_manifest_sha256=SEAL,proof='PROOF.md',proof_status='Complete ordinary q-cube-normalized theorem at each retained whole tuple; positive forward completeness; no canonical promotion.')
    index={r[0]:i for i,r in enumerate(rows)}
    cuts=dict(parent_sha256=digest(PARENT/'zero89.json'),complete_parent_to_new_rows=[dict(parent_index=i,old=row,new_index=index.get(row[0]),new=rows[index[row[0]]] if row[0] in index else None) for i,row in enumerate(old['source'])],added_rows=[dict(new_index=index['Y'],row=['Y','*','q3','s'])],deleted_names=sorted(deleted),moved_names=sorted(moved),replaced_names=sorted(replacements),coordinate_map=dict(Y='q^3*s',n_old='n_new-s'),clearing=dict(Z_old='q^3*Z_new',M_old='q^3*M_new',N_old='q^12*N_new'))
    artifacts={'zero86.json':encode(packet),'CUTS.json':encode(cuts)}
    for name in ['zero89.json','PROOF.md','MANIFEST.json','SOURCE_PINS.json','INDEXED_BINDING.json']:artifacts['parents/'+name]=(PARENT/name).read_bytes()
    artifacts['INDEXED_BINDING.json']=(PARENT/'INDEXED_BINDING.json').read_bytes()
    for p in (PARENT/'coefficients').rglob('*'):
        if p.is_file():artifacts[str(p.relative_to(PARENT))]=p.read_bytes()
    for name,blob in artifacts.items():
        target=HERE/name
        if args.check:need(target.read_bytes()==blob,'whole deterministic generated member '+name)
        else:
            need(not target.exists() or target.read_bytes()==blob,'refuse changed generated member '+name);target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(blob)
    print(json.dumps(dict(status='PASS',optimized_python=bool(sys.flags.optimize),check_mode=args.check,generated_files={n:sha256(b).hexdigest() for n,b in artifacts.items()},parent_or_incoming_code_executed=False),indent=2,sort_keys=True))
if __name__=='__main__':main()
