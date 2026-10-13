"""Solver-free replay of the twenty retained calls and already exposed rays."""
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/cc5b/Proofs/Topology/UnknotRecognition')
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import verify_crushing_recognition
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from conflict_composition_research.standard import observation


def digest(value):
    return sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def pins():
    return {str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
            for p in sorted((ROOT/'fast/fastunknot').rglob('*.py'))}


def chain_of(result):
    return result['partial_chain'] if result['status']=='INCONCLUSIVE' else result['certificate']['chain']


def replay_driver(diagram,result,config):
    if result['status']=='INCONCLUSIVE':
        assert verify_crushing_chain(diagram,result['partial_chain'])
    else:
        assert verify_crushing_recognition(diagram,result['certificate'])
        assert result['status']==result['certificate']['status']
    chain=chain_of(result)
    assert chain['schema']==('diagram-crushing-v4' if config['reduce_pachner_descent'] else 'diagram-crushing-v3')
    stats=result['stats']
    assert all(type(x) is int and x>=0 for x in stats.values())
    names={'normal-ray-crushing-v1':'crushing_steps','normal-boundary-unlayer-v1':'boundary_unlayerings',
           'normal-pachner-32-v1':'pachner32_moves','normal-pachner-descent-v1':'pachner_descent_macros'}
    counts={v:0 for v in names.values()};up=down=0
    for step in chain['steps']:
        counts[names[step['schema']]]+=1
        if step['schema']=='normal-pachner-descent-v1':
            for move in step['certificate']['moves']:
                kind=move['transport']['move']['schema']
                up+=kind=='pachner-23-v1';down+=kind=='pachner-32-v1'
    assert all(stats.get(k,0)==v for k,v in counts.items())
    assert stats['stages']==len(chain['steps'])+int(chain['triangulation'] is not None)
    if config['reduce_pachner_descent']:
        assert stats['pachner_descent_upward_moves']==up
        assert stats['pachner_descent_downward_moves']==down
    else:
        assert not any(k.startswith('pachner_descent_') for k in stats)
    caps={'max_sectors':'sectors_attempted','max_bases':'bases_attempted','max_pivots':'lp_pivots',
          'max_anchors':'anchors_tested','max_tree_nodes':'nodes_attempted','max_hitting_subsets':'hitting_subsets_tested',
          'max_ellipsoid_iterations':'lp_ellipsoid_iterations','max_feasibility_calls':'lp_feasibility_calls'}
    for cap,field in caps.items():
        if config[cap] is not None:assert stats[field]<=config[cap]
    if config['max_crushes'] is not None:assert sum(counts.values())<=config['max_crushes']
    return counts


def main():
    raw=(HERE/'audit.json').read_bytes();data=json.loads(raw);before=pins()
    assert data['passed'] is True and data['calls_completed']==20
    assert not data['failures'] and not data['unreturned_calls'] and data['active_call'] is None
    assert data['native_sha256']==before
    assert data['script_sha256']==sha256((HERE/'audit.py').read_bytes()).hexdigest()
    assert data['protocol']['total_calls']==20 and data['protocol']['no_timing_claim'] is True
    assert len(data['circle'])==2 and len(data['records'])==6
    for entry in data['circle']:
        assert entry['input_pd']==[] and entry['result']['status']=='UNKNOT'
        replay_driver(Diagram.from_pd([]),entry['result'],entry['config'])
    checked=[]
    for record in data['records']:
        diagram=Diagram.from_braid(record['braid']['strands'],record['braid']['word'])
        assert [list(row) for row in diagram.pd]==record['input_pd']
        for arm,entry in record['preprocessing'].items():
            assert arm in ('baseline','u1') and entry['config']['reduce_pachner_descent']==(arm=='u1')
            assert entry['config']['max_tree_nodes']==0 and entry['result']['status']=='INCONCLUSIVE'
            assert entry['result']['stats']['lp_calls']==entry['result']['stats']['nodes_attempted']==0
            replay_driver(diagram,entry['result'],entry['config'])
        base=chain_of(record['preprocessing']['baseline']['result'])
        chain=chain_of(record['preprocessing']['u1']['result'])
        assert base['source_triangulation']==chain['source_triangulation'] and base['shelling']==chain['shelling']
        assert base['steps']==chain['steps'][:len(base['steps'])]
        query=record['source_query'];source=query['source'];n=len(source['tetrahedra'])
        assert source==chain['triangulation'] and digest(source)==query['source_sha256']
        comp=record['endpoint_comparison']
        assert comp['baseline_tetrahedra']==len(base['triangulation']['tetrahedra'])
        assert comp['u1_tetrahedra']==n and comp['baseline_steps_literal_prefix'] is True
        assert comp['baseline_source_sha256']==digest(base['triangulation'])
        assert comp['u1_source_sha256']==digest(source)
        result=query['result'];stats=result['stats'];upper=None
        caps={'max_nodes':'nodes_attempted','max_pivots':'lp_pivots','max_anchors':'anchors_tested',
              'max_hitting_subsets':'hitting_subsets_tested','max_ellipsoid_iterations':'lp_ellipsoid_iterations',
              'max_feasibility_calls':'lp_feasibility_calls'}
        for cap,field in caps.items():assert 0<=stats[field]<=query['config'][cap]
        if result['status']=='NO_POSITIVE_EULER':
            proof=result['certificate']
            assert proof['allowed_types']==[[t,q] for t in range(n) for q in range(3)]
            assert verify_euler_branch_tree(source,proof)
            split=sorted({node['tetrahedron'] for node in proof['nodes'] if node['kind']=='split'})
            assert query['replay']['splitting_set']==split and query['replay']['h_upper_bound']==len(split)
            upper=len(split)
            assembled=query['assembled_proof']['certificate']
            assert assembled['chain']==chain and assembled['exhaustion']==proof
            assert verify_crushing_recognition(diagram,assembled)
            assert 'not a fresh whole-driver result' in query['assembled_proof']['scope']
        else:
            assert result['status']=='INCONCLUSIVE' and query['assembled_proof'] is None
            assert query['replay']['no_negative_claim'] is True
        representatives={}
        for index,point in enumerate(query['exposed_positive_points']):
            representatives.setdefault(digest(point['result']['coordinates']),(index,point))
        rays=[]
        for index,point in representatives.values():
            obs,rank=observation(source,point['result']['coordinates'])
            assert obs['canonical_euler']==point['result']['euler_characteristic']>0
            assert obs['conflicts']==point['result']['conflicts'] and obs['conflicts']
            rays.append(dict(captured_index=index,coordinates=point['result']['coordinates'],observation=obs,rank=rank))
        edges=[set(ray['observation']['conflicts']) for ray in rays]
        tested=[];witness=None;limit=10000;total=0;lower=0
        for k in range(n+1):
            count=0;exhausted=True
            for B in combinations(range(n),k):
                if total==limit:exhausted=False;break
                total+=1;count+=1
                if all(set(B)&edge for edge in edges):witness=list(B);exhausted=False;break
            if exhausted:lower=k+1
            tested.append(dict(size=k,subsets_tested=count,exhausted=exhausted))
            if witness is not None or not exhausted:break
        exact=lower if upper==lower else None
        checked.append(dict(id=record['id'],source_sha256=digest(source),tetrahedra=n,
            original_matching_replayed=True,unique_exposed_rays=rays,
            retained_hypergraph_tau=len(witness) if witness is not None else None,
            retained_hypergraph_hitting_set=witness,combination_counts=tested,
            global_h_lower_bound=lower,global_h_upper_bound=upper,exact_h=exact,
            status=result['status'],discovery_used=False))
        print(json.dumps({k:checked[-1][k] for k in ('id','tetrahedra','status','global_h_lower_bound','global_h_upper_bound','exact_h')}),flush=True)
    assert before==pins()
    output=dict(passed=True,discovery_used=False,general_quasipolynomial=False,native_sha256=before,
        audit_sha256=sha256(raw).hexdigest(),script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        standard_checker_sha256=sha256((ROOT/'fast/conflict_composition_research/standard.py').read_bytes()).hexdigest(),
        replayed_circle_whole_calls=2,replayed_preprocessing_calls=12,replayed_source_queries=6,
        assembled_negative_proofs=5,records=checked)
    (HERE/'replay.json').write_text(json.dumps(output,sort_keys=True,separators=(',',':'))+'\n')
    print('PASSED',flush=True)

if __name__=='__main__':main()
