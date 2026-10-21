#!/usr/bin/env python3
"""Replay each saved reassociation chain and both complete guarded graphs.

This proves exact source-control identity for the saved checkpoints only.
It does not validate a changed physical transition table or a shorter reset.
"""
from pathlib import Path
import hashlib,json
import control_rotation_fast219 as q

HERE=Path(__file__).resolve().parent
def tuples(x):return tuple(tuples(y)for y in x)if isinstance(x,list)else x
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    assert __debug__,'Keep assertions enabled'
    root=HERE/'reset_checkpoint';records=[]
    for path in sorted(root.glob('front_*.sites.json')):
        chain_path=path.with_name(path.name.replace('.sites.json','.chain.json'))
        chain=json.loads(chain_path.read_text());tree=q.old
        for c in chain:
            x=tuples(c['source_subtree'])
            assert x in q.q.nodes(tree),'Chain subtree absent'
            alternatives=[q.rotated(x,c['direction'],mode)for mode in(0,1)]
            matches=[a for a in alternatives if a is not None and a[1]==c['changes']]
            assert matches,'Local open-control rewrite not reproduced'
            assert all(a[0]==matches[0][0]for a in matches),'Ambiguous saved rewrite'
            tree=q.q.replace_all(tree,x,matches[0][0])
        rows=json.loads(path.read_text())
        assert q.s.tree(rows)==tree,'Saved source differs from chain'
        assert q.s.graph_intervals(rows)==q.G,'Interval CFG changed'
        assert q.s.graph_arithmetic(rows)[0]==q.G,'Arithmetic CFG changed'
        records.append({'source':path.name,'source_sha256':sha(path),
          'chain_sha256':sha(chain_path),'rotations':len(chain),
          'metrics':q.s.metrics(tree)})
    assert records,'No checkpoints'
    r={'status':'EXACT_SOURCE_REASSOCIATION_CHECKPOINT_PASS',
       'scope':'Both guarded ordinal graphs and each saved open-control rewrite; no TM runtime claim.',
       'records':records}
    (root/'audit.json').write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2))
if __name__=='__main__':main()
