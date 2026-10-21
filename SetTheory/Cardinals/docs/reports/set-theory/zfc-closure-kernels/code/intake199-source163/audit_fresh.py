#!/usr/bin/env python3
"""Output/capture audit only; does not invoke any delivered program."""
import argparse,hashlib,json
from pathlib import Path
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--actual',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    P=a.actual;read=lambda p:json.loads((P/p).read_text());r=read('actual.json')
    assert r['status']=='ALL_FOUR_SELECTED_LEAVES_PASS'and r['original_unchanged']
    names=['source-blank','matrix','pairing','credit'];assert[j['name']for j in r['jobs']]==names
    before=read('original.json');chain=before;changes=[]
    for j in r['jobs']:
        name=j['name'];assert j['returncode']==0 and not j['timed_out']and j['semantic_gates']=='PASS'
        assert j['seconds']<120 and j['timeout_seconds']==120
        b=read(name+'-before.json');c=read(name+'-after.json');assert b==chain
        actual={k:{'before':b.get(k),'after':c.get(k)}for k in set(b)|set(c)if b.get(k)!=c.get(k)}
        assert actual==j['changes']and set(actual)<=set(j['allowed_output_paths'])
        assert sha(P/'logs'/f'{name}.stdout')==j['stdout_sha256']
        assert sha(P/'logs'/f'{name}.stderr')==j['stderr_sha256']and(P/'logs'/f'{name}.stderr').read_bytes()==b''
        assert sha(P/'outputs'/f'{name}.json')==j['output_sha256'];chain=c;changes+=list(actual)
    assert chain==read('final.json')
    assert sorted(changes)==['code/theory/diagonal_matrix_check.json','code/theory/dyadic_pairing_check.json','evidence/source_blank.json']
    s=read('outputs/source-blank.json');assert s['status']=='INDEPENDENT_FINITE_SOURCE_AND_COMPLETE_BLANK_PASS'
    assert(s['working_states'],s['rows'],s['guarded_edges'])==(216,432,6175)
    assert s['source_permutation']=={'interval':[902,1185],'register_swap':[3,5],'input_entry':902,'normal_exit':1185,'inbound':[[896,902]],'outbound':[[1179,1185]]}
    assert s['row_changes']==[{'row':[199,1],'before':[1,1,166],'after':[1,1,12]},{'row':[206,0],'before':[0,1,186],'after':[0,1,76]}]
    t=s['startup'];assert(t['steps'],t['native_state'],t['canonical_state'],t['head'],t['gap'],t['unit_spares'],t['one_cells'])==(313133,84,84,-5,80,130,277)
    assert len(t['ones'])==277 and len(set(t['ones']))==277 and t['complete_zero_exterior']and t['changed_rows_absent']
    assert t['logical_registers']==[3,0,0,0,3,0,0,0,0]
    c=read('outputs/canonicalization.json');assert c['status']=='EXACT_ALL_ROW_STATE_BIJECTION_PASS'and c['all_rows_checked']==432
    m=read('outputs/matrix.json');assert m['status']=='PASS'and m['designated']==[2]and(m['truth'],m['falsity'])==(2,0)
    assert sum(v['assignments']for v in m['schemata'].values())==207 and all(v['values']==[2]for v in m['schemata'].values())
    assert(m['modus_ponens_pairs'],m['generalization_pairs'])==(9,9)
    p=read('outputs/pairing.json');assert p['status']=='FINITE_SUPPORT_CHECK_PASS'
    assert[p[k]for k in['inverse_codes','pair_rectangular_cases','bidirectional_recoding_cases','constructor_intertwining_cases']]==[100000,640,512,1024]
    assert p['order_counterexample']=={'old_le':[16,20],'recoded':[20,16]}
    d=read('outputs/credit.json');assert d['status']=='FINITE_SUPPORT_CHECK_PASS'
    assert(d['explicit_words'],d['diagonals'],d['maximum_candidate_exclusive'])==(10000,2000,2001000)
    assert d['initial_credits'][3]=={'np':3,'credit':1}
    out={'status':'FOUR_FRESH_OUTPUTS_AND_CAPTURE_CHAIN_REVIEW_PASS','reviewer':'drop_contract (also runner and pricing author)',
      'scope':'Read-only own semantic output/provenance audit. This is not a separate mathematical peer or a candidate rerun. The selected leaves are finite support and exact startup; no fresh universal primitive runtime is claimed.',
      'jobs':names,'original_files':len(before),'final_files':len(chain),'allowed_changes':sorted(changes),
      'result_counts':{'blank_steps':313133,'states':216,'rows':432,'guarded_edges':6175,'matrix_schema_assignments':207,'matrix_inference_pairs':18,'inverse_codes':100000,'explicit_words':10000,'complete_diagonals':2000},
      'inputs':{str(p.relative_to(P)):sha(p)for p in sorted(P.rglob('*'))if p.is_file()and'work'not in p.relative_to(P).parts},'auditor_sha256':sha(Path(__file__))}
    assert not a.output.exists();a.output.write_text(json.dumps(out,indent=2)+'\n');print(out['status'])
if __name__=='__main__':main()
