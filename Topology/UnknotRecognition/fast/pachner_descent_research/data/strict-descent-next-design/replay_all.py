"""Fresh solver-free replay of every retained scratch source and witness."""
from hashlib import sha256
from itertools import combinations
import gzip
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/cc5b/Proofs/Topology/UnknotRecognition')
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.pachner_cover_verify import inspect_pachner_descent
from conflict_composition_research.standard import observation
from strict_pachner32_research.check_evidence import check_archive


def pins():
    return {str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
            for p in sorted((ROOT/'fast/fastunknot').rglob('*.py'))}


def digest(x):
    return sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def main():
    before=pins();files={};prime=[];descent=[]
    archive_summary=check_archive()
    archive_path=ROOT/'fast/strict_pachner32_research/data/generation/euler-queries.json.gz'
    archived=json.loads(gzip.decompress(archive_path.read_bytes()))
    def load(name):
        path=HERE/(name+'.json');raw=path.read_bytes();files[path.name]=sha256(raw).hexdigest()
        x=json.loads(raw);assert x['passed'] is True and x['native_sha256']==before
        return x
    for name in ('T25','T27','W34'):
        prep=load(name+'-preprocess')['record'];query=load(name+'-query')['record']
        source=prep['source'];assert source==query['source']
        assert digest(source)==prep['source_sha256']==query['source_sha256']
        diagram=Diagram.from_braid(prep['braid']['strands'],prep['braid']['word'])
        assert [list(row) for row in diagram.pd]==prep['input_pd']
        chain=prep['result']['partial_chain'];assert chain['schema']=='diagram-crushing-v3'
        assert verify_crushing_chain(diagram,chain) and chain['triangulation']==source
        assert prep['config']['max_tree_nodes']==0
        assert prep['result']['stats']['lp_calls']==prep['result']['stats']['nodes_attempted']==0
        p=_prepare(source,lambda:None);assert p['vertices']==1
        classes={}
        for i,root in enumerate(p['edge_roots']):classes.setdefault(root,[]).append(i)
        eligible=[root for root,locals in classes.items() if root not in p['boundary_incidence']
                  and len(locals)==3 and len({i//6 for i in locals})==3]
        assert eligible==[] and prep['pachner32_terminal']['stats']['scan_complete'] is True
        result=query['result'];upper=None
        if result['status']=='NO_POSITIVE_EULER':
            proof=result['certificate']
            assert proof['allowed_types']==[[t,q] for t in range(len(source['tetrahedra'])) for q in range(3)]
            assert verify_euler_branch_tree(source,proof)
            splits={node['tetrahedron'] for node in proof['nodes'] if node['kind']=='split'}
            upper=len(splits);assert upper==query['replay']['h_upper_bound']
        else:
            assert result['status']=='INCONCLUSIVE' and query['replay']['no_negative_claim'] is True
        lower=0;rank_count=0
        if name!='W34':
            evidence=load(name+'-exposed-replay');assert evidence['source_sha256']==digest(source)
            assert evidence['query_sha256']==files[name+'-query.json']
            conflicts=[]
            for ray in evidence['unique_exposed_rays']:
                exposed=query['exposed_positive_points'][ray['captured_index']]
                assert ray['coordinates']==exposed['result']['coordinates']
                info,rank=observation(source,ray['coordinates'])
                assert info==ray['observation'] and rank==ray['rank'] and info['canonical_euler']>0
                assert info['conflicts']==exposed['result']['conflicts']
                assert all([t,q] in exposed['mask'] for t,row in enumerate(ray['coordinates'])
                           for q in range(3) if row[4+q])
                conflicts.append(set(info['conflicts']));rank_count+=1
            for k in range(4):
                hit=next((B for B in combinations(range(len(source['tetrahedra'])),k)
                          if all(set(B)&edge for edge in conflicts)),None)
                if hit is not None:
                    lower=k;break
            else:raise AssertionError('retained conflicts no longer have expected small hitting set')
            assert lower==evidence['retained_hypergraph_tau']==evidence['global_h_lower_bound']==3
        assert upper==({'T25':3,'T27':None,'W34':None}[name])
        prime.append(dict(id=name,tetrahedra=len(source['tetrahedra']),source_sha256=digest(source),
            v3_chain_verified=True,strict32_exhausted=True,euler_status=result['status'],
            h_lower_bound=lower,h_upper_bound=upper,exact_h=lower if lower==upper else None,
            exposed_root_rays_verified=rank_count))
    for index,name in enumerate(('T8','F12','TT17')):
        d=load(name+'-descent')['record'];source=d['source']
        assert source==archived['records'][index]['source']
        assert d['historical_source_archive_sha256']==sha256(archive_path.read_bytes()).hexdigest()
        assert digest(source)==d['source_sha256'] and d['heights']==[[0]*4 for _ in source['tetrahedra']]
        assert d['result']['status']=='DESCENT_FOUND'
        r=inspect_pachner_descent(source,d['heights'],d['result']['certificate'],max_upward=1)
        assert r==d['replay']['summary'] and r['upward_moves']==1 and r['downward_moves']==2
        assert len(d['result']['certificate']['moves'])==3
        assert all(not any(row) for row in r['heights'])
        assert r['final_tetrahedra']==r['initial_tetrahedra']-1
        assert d['result']['stats']['nodes']<=d['config']['max_nodes']==256
        assert d['result']['stats']['aggregate_work']<=d['config']['max_work']==200000
        descent.append(dict(id=name,source_sha256=digest(source),before=r['initial_tetrahedra'],
            after=r['final_tetrahedra'],upward_moves=1,downward_moves=2,verified=True))
    assert before==pins()
    output=dict(passed=True,native_sha256=before,files_sha256=files,
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        historical_archive_fresh_replay=archive_summary,
        standard_checker_sha256=sha256((ROOT/'fast/conflict_composition_research/standard.py').read_bytes()).hexdigest(),
        prime_sources=prime,local_descents=descent,discovery_used=False,
        general_quasipolynomial=False)
    (HERE/'fresh-replay.json').write_text(json.dumps(output,sort_keys=True,separators=(',',':'))+'\n')
    print(json.dumps(dict(passed=True,prime_sources=prime,local_descents=descent,discovery_used=False)))


if __name__=='__main__':main()
