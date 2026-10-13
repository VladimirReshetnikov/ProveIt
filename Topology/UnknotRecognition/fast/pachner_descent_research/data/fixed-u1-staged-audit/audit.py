"""Twenty staged calls; distinct from a whole-recognition timing comparison."""
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
from unittest.mock import patch

HERE=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/cc5b/Proofs/Topology/UnknotRecognition')
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import recognize_by_crushing,verify_crushing_recognition
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.normal_euler_tree import _EulerMaskOracle
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree

ARMS=('baseline','u1')
SPECS=(('T',2,[1]*3),('F',3,[1,-2]*2),('TT',3,[1]*3+[2]*3),
       ('T25',2,[1]*5),('T27',2,[1]*7),('W34',3,[1,-2]*4))
QUERY=dict(strategy='envelope',candidate_policy='conflicts',max_nodes=256,
    max_pivots=10000,max_anchors=10000,max_hitting_subsets=10000,
    lp_policy='polynomial',lp_fast_path_pivots=None,
    max_ellipsoid_iterations=10000,max_feasibility_calls=10000)


def options(arm,preprocessing):
    return dict(max_sectors=256,max_bases=10000,max_crushes=None,
        sector_order='diversified',sector_quantum=64,sector_method='transversal',
        max_pivots=10000,max_anchors=10000,lp_strategy='envelope',
        reduce_vertices=True,unlayer_boundary=True,reduce_pachner32=True,
        reduce_pachner_descent=arm=='u1',max_tree_nodes=0 if preprocessing else 256,
        tree_model='source',max_hitting_subsets=10000,transversal_candidate_policy='conflicts',
        lp_policy='polynomial',lp_fast_path_pivots=None,
        max_ellipsoid_iterations=10000,max_feasibility_calls=10000)


def pins():
    return {str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
            for p in sorted((ROOT/'fast/fastunknot').rglob('*.py'))}


def digest(x):
    return sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def save(x):
    (HERE/'audit.json').write_text(json.dumps(x,sort_keys=True,separators=(',',':'))+'\n')


def replay_driver(diagram,result,config):
    if result['status']=='INCONCLUSIVE':
        chain=result['partial_chain'];assert verify_crushing_chain(diagram,chain)
    else:
        assert result['status'] in ('UNKNOT','KNOTTED')
        assert verify_crushing_recognition(diagram,result['certificate'])
        chain=result['certificate']['chain']
    assert chain['schema']==('diagram-crushing-v4' if config['reduce_pachner_descent'] else 'diagram-crushing-v3')
    schemas={'normal-ray-crushing-v1':'crushing_steps',
        'normal-boundary-unlayer-v1':'boundary_unlayerings',
        'normal-pachner-32-v1':'pachner32_moves',
        'normal-pachner-descent-v1':'pachner_descent_macros'}
    counts={s:0 for s in schemas.values()};up=down=0
    for step in chain['steps']:
        counts[schemas[step['schema']]]+=1
        if step['schema']=='normal-pachner-descent-v1':
            for move in step['certificate']['moves']:
                kind=move['transport']['move']['schema']
                up+=kind=='pachner-23-v1';down+=kind=='pachner-32-v1'
    stats=result['stats'];assert all(type(v) is int and v>=0 for v in stats.values())
    assert all(stats.get(k,0)==v for k,v in counts.items())
    if config['reduce_pachner_descent']:
        assert stats['pachner_descent_upward_moves']==up
        assert stats['pachner_descent_downward_moves']==down
        assert stats['pachner_descent_macros']<=stats['pachner_descent_calls']<=stats['stages']
    else:
        assert not any(k.startswith('pachner_descent_') for k in stats)
    assert stats['stages']==len(chain['steps'])+int(chain['triangulation'] is not None)
    caps={'max_sectors':'sectors_attempted','max_bases':'bases_attempted',
          'max_pivots':'lp_pivots','max_anchors':'anchors_tested','max_tree_nodes':'nodes_attempted',
          'max_hitting_subsets':'hitting_subsets_tested',
          'max_ellipsoid_iterations':'lp_ellipsoid_iterations','max_feasibility_calls':'lp_feasibility_calls'}
    for cap,field in caps.items():assert stats[field]<=config[cap]
    if config['max_crushes'] is not None:assert sum(counts.values())<=config['max_crushes']
    return dict(proof_verified=True,chain_schema=chain['schema'],reductions=counts,
        elementary_macro_upward_moves=up,elementary_macro_downward_moves=down,
        final_tetrahedra=None if chain['triangulation'] is None else len(chain['triangulation']['tetrahedra']))


def main():
    before=pins()
    output=dict(schema='fixed-u1-staged-audit-v1',passed=False,native_sha256=before,
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        protocol=dict(circle_whole_calls=2,preprocessing_only_calls=12,
            enabled_endpoint_queries=6,total_calls=20,no_timing_claim=True,
            source_query_stats_scope='Separate supplied-source call; never summed into alleged whole-recognition stats.'),
        circle=[],records=[],calls_completed=0,active_call=None,unreturned_calls=[],failures=[])
    save(output)

    def begin(phase,name,arm=None):
        output['active_call']=dict(phase=phase,id=name,arm=arm);save(output)
        print(json.dumps(dict(start=output['active_call'])),flush=True)

    def finish():
        assert before==pins(),'native source changed during audit'
        output['calls_completed']+=1;output['active_call']=None;save(output)

    try:
        circle=Diagram.from_pd([])
        for arm in ARMS:
            config=options(arm,False);begin('whole-circle','circle',arm)
            saved=dict(arm=arm,input_pd=[],config=config,result=None,replay=None)
            output['circle'].append(saved)
            result=recognize_by_crushing(circle,**config)
            saved['result']=result;output['active_call']['returned']=True;save(output)
            replay=replay_driver(circle,result,config)
            saved['replay']=replay
            finish();print(json.dumps(dict(done='circle',arm=arm,status=result['status'],replay=replay)),flush=True)
        for name,strands,word in SPECS:
            diagram=Diagram.from_braid(strands,word)
            record=dict(id=name,braid=dict(strands=strands,word=word),
                input_pd=[list(row) for row in diagram.pd],preprocessing={},source_query=None)
            output['records'].append(record)
            for arm in ARMS:
                config=options(arm,True);begin('preprocessing',name,arm)
                saved=dict(config=config,result=None,replay=None)
                record['preprocessing'][arm]=saved
                result=recognize_by_crushing(diagram,**config)
                saved['result']=result;output['active_call']['returned']=True;save(output)
                replay=replay_driver(diagram,result,config)
                saved['replay']=replay
                finish()
                assert result['status']=='INCONCLUSIVE'
                assert result['stats']['lp_calls']==result['stats']['nodes_attempted']==0
                p=_prepare(result['partial_chain']['triangulation'],lambda:None)
                assert p['vertices']==1
                print(json.dumps(dict(done=name,phase='preprocessing',arm=arm,
                    tetrahedra=replay['final_tetrahedra'],reductions=replay['reductions'])),flush=True)
            base=record['preprocessing']['baseline']['result']['partial_chain']
            chain=record['preprocessing']['u1']['result']['partial_chain']
            assert base['source_triangulation']==chain['source_triangulation'] and base['shelling']==chain['shelling']
            assert base['steps']==chain['steps'][:len(base['steps'])]
            source=chain['triangulation']
            record['endpoint_comparison']=dict(baseline_tetrahedra=len(base['triangulation']['tetrahedra']),
                u1_tetrahedra=len(source['tetrahedra']),baseline_steps_literal_prefix=True,
                baseline_source_sha256=digest(base['triangulation']),u1_source_sha256=digest(source))
            save(output)
        for record in output['records']:
            name=record['id'];diagram=Diagram.from_pd(record['input_pd'])
            chain=record['preprocessing']['u1']['result']['partial_chain'];source=chain['triangulation']
            exposed=[];original=_EulerMaskOracle.attempt

            def observe(self,mask):
                result=original(self,mask)
                if result['status']=='POSITIVE':
                    exposed.append(dict(mask=[list(pair) for pair in mask],result=deepcopy(result)))
                return result

            begin('enabled-endpoint-query',name,'u1')
            with patch.object(_EulerMaskOracle,'attempt',observe):
                result=search_euler_transversal(source,**QUERY)
            answer=dict(source=source,source_sha256=digest(source),config=QUERY,result=result,
                exposed_positive_points=exposed,replay=dict(status=result['status']),assembled_proof=None)
            record['source_query']=answer
            output['active_call']['returned']=True;save(output)
            if result['status']=='NO_POSITIVE_EULER':
                proof=result['certificate']
                assert proof['allowed_types']==[[t,q] for t in range(len(source['tetrahedra'])) for q in range(3)]
                assert verify_euler_branch_tree(source,proof)
                splits=sorted({node['tetrahedron'] for node in proof['nodes'] if node['kind']=='split'})
                certificate=dict(schema='diagram-crushing-recognition-v2',status='KNOTTED',chain=chain,exhaustion=proof)
                assert verify_crushing_recognition(diagram,certificate)
                answer['replay'].update(full_root_negative_verified=True,splitting_set=splits,h_upper_bound=len(splits))
                answer['assembled_proof']=dict(scope='Assembled from authenticated preprocessing-only partial chain and this separate supplied-source query; not a fresh whole-driver result.',
                    certificate=certificate,verified=True)
            elif result['status']=='POSITIVE_EULER':
                a=_coordinates(_prepare(source,lambda:None),result['coordinates'],lambda:None)
                assert a['euler_characteristic']==result['euler_characteristic']>0
                answer['replay']['admissible_positive_verified']=True
            else:
                assert result['status']=='INCONCLUSIVE'
                answer['replay']['no_negative_claim']=True
            finish();print(json.dumps(dict(done=name,phase='enabled-endpoint-query',status=result['status'],
                replay=answer['replay'],nodes=result['stats']['nodes_attempted'],pivots=result['stats']['lp_pivots'])),flush=True)
        assert output['calls_completed']==20 and before==pins()
        output['passed']=True;save(output);print('PASSED',flush=True)
    except BaseException as error:
        failure=dict(call=output['active_call'],error_type=type(error).__name__,message=str(error))
        output['failures'].append(failure)
        if output['active_call'] is not None and not output['active_call'].get('returned',False):
            output['unreturned_calls'].append(failure)
        save(output);raise


if __name__=='__main__':main()
