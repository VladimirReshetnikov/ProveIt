#!/usr/bin/env python3
"""Independent optional-duration and small generic two-register checks."""
from pathlib import Path
from collections import Counter
from fractions import Fraction
import json,sys,hashlib,os,argparse
sys.dont_write_bytecode=True
A=Path(__file__).resolve().parent
_parser=argparse.ArgumentParser(description=__doc__)
_parser.add_argument('packet_root', nargs='?', default=os.environ.get('RESET_NET_PACKET_ROOT', str(A.parent)), help='Reset-net packet root; defaults to RESET_NET_PACKET_ROOT or the parent of this script directory')
R=Path(_parser.parse_args().packet_root).expanduser().resolve()
if not (R/'reset_net.json').is_file():
    _parser.error('packet_root must contain reset_net.json')
sys.path.insert(0,str(R))
import peak_quadratic,source_quadratic,build_net

def expand(p,a):
    terms=[('constant',a['constant'])]+[(f'v{i}',c) for i,c in a['variables']]+[('p'+k,c) for k,c in a['parameters']]
    for f,c in a['forms']:terms += [(f'v{i}',d*c) for i,d in p['linear_forms'][f]]
    d=Counter()
    for k,c in terms:d[k]+=c
    return {k:c for k,c in d.items() if c}
def evaluate(p,w,pars):
    def ev(a):return sum(c*(1 if k=='constant' else pars[k[1:]] if k[0]=='p' else w.get(int(k[1:]),0)) for k,c in expand(p,a).items())
    total=sum(ev(x['affine'])**2 for x in p['affine_squares'])
    for x in p['quadratic_products']:
        left,right=ev(x['left']),ev(x['right']);assert left>=0 and right>=0;total+=left*right
    return total
program=json.loads((R/'source/virtual3.json').read_text());table=source_quadratic.semantic_table(program)
for h in (1,2,3):
    small=peak_quadratic.compile_peak(table,h);p=peak_quadratic.compile_peak(table,h,all_durations=True)
    assert 'not equivalent' in p['domain'] and 'half-integral' in p['domain']
    assert p['variables']['count']==2813*h+1 and p['variables']['padding_index']==2813*h
    assert len(p['affine_squares'])==6*h+2 and len(p['quadratic_products'])==762*h
    assert p['linear_forms']==small['linear_forms'] and p['quadratic_products']==small['quadratic_products']
    assert p['affine_squares'][:-1]==small['affine_squares'][:-1]
    lhs=expand(p,p['affine_squares'][-1]['affine']);expected=expand(small,small['affine_squares'][-1]['affine']);expected[f'v{2813*h}']=-2
    assert lhs==expected
    nodur=peak_quadratic.compile_peak(table,h,with_duration=False)
    assert 'N' not in nodur['parameters'] and len(nodur['affine_squares'])==6*h+1 and 'not a parameter' in nodur['scope']
assert json.loads((R/'all_duration_schema_h1.json').read_text())==peak_quadratic.compile_peak(table,1,all_durations=True)
# The full optional witness is exactly the independently audited h=328 minimum witness plus z=1.
w0=json.loads((R/'accepting_peak_witness.json').read_text());w1=json.loads((R/'accepting_all_duration_witness_N390.json').read_text())
assert w1['parameters']=={'L':6,'R':0,'N':390} and w1['variable_count']==922665
want=dict(w0['nonzero_coordinates']);want[922664]=1
assert dict(w1['nonzero_coordinates'])==want
h=328;H=11;B=6;v=want[922663];assert v==14
assert 390-h-3*H+B-2*v-5-2*want[922664]==0
assert 389-h-3*H+B-2*v-5-2*Fraction(1,2)==0
assert all(389-h-3*H+B-2*v-5-2*z!=0 for z in range(30))
# Two-counter program: increment L then conditional decrement L, both arms halt.
# The nonzero source execution returns to its initial mass after a one-token peak.
toy={'registers':['L','R'],'entry':'q0','halt':'HALT','rows':{'q0':['ADD',0,'q1'],'q1':['SUB',0,'HALT','HALT']}}
tt=source_quadratic.semantic_table(toy);tn=build_net.compile_net(toy,initial_affine={'L':{'L':1},'R':{'R':1},'budget':{'L':1,'R':1},'q:START':{'constant':1}},parameters=['L','R'])
try:
    build_net.compile_net(toy)
except ValueError:
    pass
else:
    raise AssertionError('Different register interface silently accepted default input map')
assert len(tn['places'])==11 and len(tn['transitions'])==11
assert sum(len(t['pre'])+len(t['post']) for t in tn['transitions'])==34 and sum(len(t['reset']) for t in tn['transitions'])==1
assert set(tn['initial_affine'])<=set(tn['places'])
assert tn['controls']==['q0','q1','HALT','START','CLEAN_R','DRAIN','DONE']
# Manual witness indices: three selectors plus five retained bases per step.
for L in range(4):
    for Rinput in range(4):
        initial=['L','R'];B=L+Rinput;N=2*B+8
        p=peak_quadratic.compile_peak(tt,2,initial=initial)
        assert p['variables']['count']==20 and p['ledger']=={'natural_witnesses':20,'affine_squares':12,'quadratic_products':8,'degree_at_most':2}
        w={0:1,3:L,4:Rinput,9:1,13:L,14:Rinput,16:1,19:1}
        assert evaluate(p,w,{'L':L,'R':Rinput,'N':N})==0
        assert evaluate(p,w,{'L':L,'R':Rinput,'N':N+1})>0
        pa=peak_quadratic.compile_peak(tt,2,initial=initial,all_durations=True);wa={**w,20:1}
        assert evaluate(pa,wa,{'L':L,'R':Rinput,'N':N+2})==0
        assert evaluate(pa,{**w,20:Fraction(1,2)},{'L':L,'R':Rinput,'N':N+1})==0
# Affine initial mass with a constant: raw_A,2 has B=raw_A+2 and the same source horizon.
p=peak_quadratic.compile_peak(tt,2,initial=['raw_A',2]);w={0:1,3:3,4:2,9:1,13:3,14:2,16:1,19:1}
assert evaluate(p,w,{'raw_A':3,'N':18})==0
assert expand(p,p['affine_squares'][-1]['affine'])['constant']==-4
# New generic builder preserves complete original net exactly.
assert build_net.compile_net(program)==json.loads((R/'reset_net.json').read_text())
assert peak_quadratic.compile_peak(table,1)==json.loads((R/'canonical_peak_schema_h1.json').read_text())
result={'status':'PASS','all_duration_coefficients_horizons':[1,2,3],'all_duration_metadata':'Correctly natural-only; R+ parity failure explicit','full_h328_N390_fixture':'Exactly audited minimum witness plus padding z=1, 922665 slots','fractional_counterexample':'Same source/peak witness with N389,z=1/2 has zero polynomial; no natural padding exists','generic_two_register_initial_pairs':16,'generic_two_register_constant_initial_test':True,'generic_two_register_ledger':{'source_steps':2,'variables':20,'squares':12,'products':8,'toy_net_places':11,'toy_net_transitions':11,'ordinary_arcs':34,'reset_arcs':1},'three_register_literal_net_and_default_schema_unchanged':True,'sha256':{f:hashlib.sha256((R/f).read_bytes()).hexdigest() for f in ['build_net.py','peak_quadratic.py','all_duration_schema_h1.json','accepting_all_duration_witness_N390.json']}}
(A/'PADDING_AND_GENERIC_PEAK_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
