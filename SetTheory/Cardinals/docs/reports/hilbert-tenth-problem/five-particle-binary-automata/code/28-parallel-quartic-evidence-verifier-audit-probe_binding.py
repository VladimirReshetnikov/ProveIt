"""Independent negative/limitation probes; never writes the audited source tree."""
from pathlib import Path
import argparse, ast, copy, hashlib, importlib.util, json, sys
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-dir',type=Path,default=Path(__file__).resolve().parents[2]/'parallel-diophantine-certificate-research-20261003')
ROOT=parser.parse_args().source_dir.resolve()
OUT=Path(__file__).resolve().parent
class RejectCompiler:
    def find_spec(self,fullname,path=None,target=None):
        if fullname.split('.')[0] in {'compiler','circuit'}:
            raise RuntimeError('compiler/circuit import attempted')
sys.meta_path.insert(0,RejectCompiler())
spec=importlib.util.spec_from_file_location('standalone_verifier_under_audit',ROOT/'verify_example.py')
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
base=[json.loads((ROOT/name).read_text()) for name in ('example-pair-quartic.json','example-pair-sos.json','example-pair-witness.json')]
original=copy.deepcopy(base)
positive=v.verify(*base,mutate=False)
if base!=original:raise RuntimeError('valid verification mutated caller data')
cases=[]
def field(i,k,value):return lambda d:d[i].__setitem__(k,value)
def entry(i,k,j,value):return lambda d:d[i][k].__setitem__(j,value)
cases.extend([
('input_tuple',field(2,'input',tuple(base[2]['input']))),
('target_string',field(2,'target','16')),
('negative_natural_external',entry(2,'values',0,-1)),
('negative_natural_last',entry(2,'values',-1,-1)),
('bool_natural_last',entry(2,'values',-1,True)),
('float_natural_last',entry(2,'values',-1,float(base[2]['values'][-1]))),
('noncanonical_signed_pair',lambda d:(d[2]['values'].__setitem__(0,1),d[2]['values'].__setitem__(1,1))),
('both_input_counts_disagree',lambda d:(d[0].__setitem__('input_count',4),d[1].__setitem__('input_count',4))),
('variable_count_string',field(0,'variable_count',str(len(base[2]['values'])))),
('duplicate_names',entry(1,'variable_names',1,base[1]['variable_names'][0])),
('names_tuple',field(1,'variable_names',tuple(base[1]['variable_names']))),
('values_tuple',field(2,'values',tuple(base[2]['values']))),
('ledger_not_object',field(1,'ledger',[])),
('extra_sos_field',field(1,'extra',0)),
('extra_witness_field',field(2,'extra',0)),
('missing_quartic_format',lambda d:d[0].pop('format')),
('missing_sos_format',lambda d:d[1].pop('format')),
('quartic_degree_five',lambda d:d[0]['terms'].append([1,[0]*5])),
('residual_degree_three',lambda d:d[1]['residuals'][0].append([1,[0]*3])),
('quartic_index_negative',lambda d:d[0]['terms'].append([1,[-1]])),
('quartic_index_out_of_range',lambda d:d[0]['terms'].append([1,[len(d[2]['values'])]])),
('residual_coefficient_bool',lambda d:d[1]['residuals'][0][0].__setitem__(0,True)),
('residual_coefficient_float',lambda d:d[1]['residuals'][0][0].__setitem__(0,float(d[1]['residuals'][0][0][0]))),
('quartic_zero_coefficient',lambda d:d[0]['terms'][0].__setitem__(0,0)),
('residual_zero_coefficient',lambda d:d[1]['residuals'][0][0].__setitem__(0,0)),
('duplicate_residual_term',lambda d:d[1]['residuals'][0].append(copy.deepcopy(d[1]['residuals'][0][0]))),
('unsorted_quartic_monomial',lambda d:d[0]['terms'].append([1,[1,0]])),
('unsorted_residual_monomial',lambda d:d[1]['residuals'][0].append([1,[1,0]])),
('quartic_not_literal_sos',lambda d:d[0]['terms'][0].__setitem__(0,d[0]['terms'][0][0]+1)),
('missing_residual_changes_sos',lambda d:d[1]['residuals'].pop()),
('nonzero_last_auxiliary_residual',entry(2,'values',-1,base[2]['values'][-1]+1)),
])
rejected={}
for label,change in cases:
    data=copy.deepcopy(base);change(data);before=copy.deepcopy(data)
    try:v.verify(*data,mutate=False)
    except v.ValidationError as exc:rejected[label]=str(exc)
    else:raise RuntimeError('invalid case accepted: '+label)
    if data!=before:raise RuntimeError('invalid verification mutated caller data: '+label)
# Establish exact scope of schema assertion: ledger contents and display names are unbound.
accepted={}
for label,change in [
('arbitrary_ledger_contents',field(1,'ledger',{'deliberately_unchecked':True})),
('arbitrary_unique_display_names',field(1,'variable_names',[f'renamed_{i}' for i in range(len(base[2]['values']))])),
]:
    data=copy.deepcopy(base);change(data);accepted[label]=v.verify(*data,mutate=False)['status']
# The schema intentionally describes any algebraic certificate, not exclusively the emitted example.
empty=[{'format':'sparse-integer-polynomial-v1','input_count':0,'variable_count':0,'terms':[]},
{'format':'natural-quartic-sos-v1','input_count':0,'variable_names':[],'residuals':[],'ledger':{}},
{'input':[],'target':[],'values':[]}]
accepted['empty_dimension_zero_certificate']=v.verify(*empty,mutate=False)['status']
imports=[]
for node in ast.walk(ast.parse((ROOT/'verify_example.py').read_text())):
    if isinstance(node,ast.Import):imports.extend(x.name for x in node.names)
    elif isinstance(node,ast.ImportFrom):imports.append(node.module)
result={'status':'PASS','optimized':not __debug__,'negative_cases':len(rejected),'rejected_cases':rejected,'accepted_scope_probes':accepted,'imports':sorted(imports),'compiler_circuit_import_guard':'PASS','caller_data_unchanged':'PASS','positive':positive,'verifier_sha256':hashlib.sha256((ROOT/'verify_example.py').read_bytes()).hexdigest()}
name='independent-probes-optimized.json' if not __debug__ else 'independent-probes.json'
(OUT/name).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':result['status'],'optimized':result['optimized'],'negative_cases':len(rejected),'accepted_scope_probes':accepted}))
