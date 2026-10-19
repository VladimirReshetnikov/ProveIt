#!/usr/bin/env python3
"""Portable reconstruction of the source re-encoding that enables 236 states.

This check proves exact SOURCE control-graph equality, and reconstructs the
237-state intermediate byte for byte. It does not certify binary runtime; the
separate quantified runtime and blank-startup certificates provide that link.
Run without -O or -OO, from any working directory, with Python 3.
"""
from pathlib import Path
import hashlib
import json
import sys
import importlib.util

HERE=Path(__file__).resolve().parent
PIN='1b27f052d770f4c7d435e82e779bf21f5a1f66ed'
BASE_SOURCE_SHA='7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
BASE_TABLE_SHA='a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a'
ROTATED_TABLE_SHA='da0b3d1fdd74d56482b9d231119bbbaccdbcadc78e7b7df72c3a734a3a808724'
PREFIX='1110100100110110101010011100001'
CHANGES={
    (177,0):((0,'R',165),(0,'R',185)),
    (177,1):((1,'R',185),(1,'R',212)),
    (185,0):((0,'R',192),(0,'R',165)),
    (185,1):((1,'R',212),(1,'R',192)),
}

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def closed(t):
    for p,o,r in g.sites_of_tree(t):
        if o=='CH':return False
        if o=='CD' and p.count('0')<1:return False
        if o=='CB' and p.count('0')<r:return False
        if o=='CC' and p.count('1')<r:return False
    return True

def main():
    if not __debug__ or sys.flags.optimize:raise SystemExit('Run without -O/-OO.')
    global g
    spec=importlib.util.spec_from_file_location('independent_source_checker',HERE/'check_rotation_certificate.py')
    g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
    baseline=HERE/'baseline_sites.json';base_table=HERE/'baseline237_old.tm'
    assert sha(baseline)==BASE_SOURCE_SHA and sha(base_table)==BASE_TABLE_SHA
    ss=json.loads(baseline.read_text());t=g.tree_of_sites(ss);n=t
    for bit in PREFIX:n=n[int(bit)]
    P,tail=n;Q,R=tail
    assert all(closed(x) for x in (P,Q,R))
    chunk_counts=[len(g.sites_of_tree(x)) for x in (P,Q,R)]
    assert chunk_counts==[245,160,132]
    cert={
      'format':'busy-beaver-source-rotation-certificate-v1',
      'baseline_sha256':BASE_SOURCE_SHA,
      'baseline_repository_commit':PIN,
      'steps':[{'number':1,'direction':'left','paths':[PREFIX]}],
    }
    certpath=HERE/'rotation_certificate.json'
    certpath.write_text(json.dumps(cert,indent=2)+'\n')
    u=g.rotate_stage(t,cert['steps'][0]);us=[list(x) for x in g.sites_of_tree(u)]
    assert [x[1:] for x in ss]==[x[1:] for x in us]
    assert len(ss)==len(us)==6455
    changed=[i for i,(old,new) in enumerate(zip(ss,us)) if old[0]!=new[0]]
    assert len(changed)==sum(chunk_counts)==537
    candidate=HERE/'rotated_sites.json';candidate.write_text(json.dumps(us,indent=2)+'\n')
    report=g.check(baseline,certpath,candidate)
    assert report['status']=='PASS_EXACT_SOURCE_CONTROL_CERTIFICATE'
    assert g.graph(t)==g.graph(u)
    assert report['final']['dag_nodes']==224
    assert report['final']['internal_source_nodes']==201
    assert report['final']['leaf_kinds']==23
    assert report['final']['max_path']==49
    assert report['final']['max_zero_run']==6
    rows={}
    for line in base_table.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,r=line.split();key=int(q),int(b)
        assert key not in rows;rows[key]=int(w),d,int(r)
    assert len(rows)==474
    for key,(old,new) in CHANGES.items():assert rows[key]==old;rows[key]=new
    raw='#! start 95\n'+''.join(f'{q} {b} {w} {d} {r}\n' for (q,b),(w,d,r) in sorted(rows.items()))
    path=HERE/'rotated237_old.tm';path.write_text(raw)
    assert sha(path)==ROTATED_TABLE_SHA
    assert len({q for q,b in rows})==237
    report.update(
      baseline_repository_commit=PIN,
      independent_checker_sha256=sha(HERE/'check_rotation_certificate.py'),
      reconstruction_script_sha256=sha(Path(__file__)),
      baseline_table_sha256=BASE_TABLE_SHA,
      rotated237_table_sha256=sha(path),
      rotated_source_sha256=sha(candidate),
      rotation_prefix=PREFIX,
      closed_chunk_leaf_counts=chunk_counts,
      all_three_chunks_syntactically_closed=True,
      changed_path_count=len(changed),
      changed_leaf_index_range=[min(changed),max(changed)],
      source_seed_binding={
        'entry_leaf':0,
        'initial_pc':'',
        'logical_registers':[3,0,0,0,3,0,0,0,0],
        'reason':'Identical ordered source control graph for every natural register vector, hence for this inherited seed.'},
      decoder_edits=[dict(state=q,read=b,old=old,new=new) for (q,b),(old,new) in sorted(CHANGES.items())],
      binary_runtime_scope='Separate unbounded literal-table runtime and exact blank-startup certificates are required.'
    )
    (HERE/'source_receipt.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ['status','rotated_source_sha256','rotated237_table_sha256','stages','local_rotations','guards_or_edges_checked_per_stage','changed_path_count','closed_chunk_leaf_counts','final']},indent=2))

if __name__=='__main__':main()
