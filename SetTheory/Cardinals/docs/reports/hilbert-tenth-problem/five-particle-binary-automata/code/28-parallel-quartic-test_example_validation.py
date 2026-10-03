"""Negative binding/schema regressions for the standalone algebraic verifier."""
from pathlib import Path
import argparse,copy,json,time,hashlib
from verify_example import verify,ValidationError
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output-dir',type=Path,default=ROOT)
OUT=parser.parse_args().output_dir.resolve();OUT.mkdir(parents=True,exist_ok=True)
start=time.perf_counter()
base=[json.loads((ROOT/name).read_text())for name in('example-pair-quartic.json','example-pair-sos.json','example-pair-witness.json')]
verify(*base,mutate=False)
cases=[]
def set_field(which,key,value):
    return lambda data:data[which].__setitem__(key,value)
for which in(0,1):
    for label,value in(('bool',True),('float',8.0),('negative',-1),('string','8'),('disagree',4)):
        cases.append((f'input_count_{which}_{label}',set_field(which,'input_count',value)))
for label,value in(('bool',True),('float',float(len(base[2]['values']))),('negative',-1),('disagree',len(base[2]['values'])-1)):
    cases.append(('variable_count_'+label,set_field(0,'variable_count',value)))
cases.extend([
 ('input_bool',lambda d:d[2]['input'].__setitem__(0,False)),
 ('input_float',lambda d:d[2]['input'].__setitem__(0,0.0)),
 ('target_bool',lambda d:d[2]['target'].__setitem__(0,True)),
 ('target_float',lambda d:d[2]['target'].__setitem__(0,1.0)),
 ('combined_bool_arity_wrong_target',lambda d:(d[0].__setitem__('input_count',True),d[2].__setitem__('target',[100,200]))),
 ('target_metadata_full_mismatch',set_field(2,'target',[100,200])),
 ('input_metadata_mismatch',lambda d:d[2]['input'].__setitem__(0,-1)),
 ('target_metadata_mismatch',lambda d:d[2]['target'].__setitem__(1,7)),
 ('unequal_metadata_masses',lambda d:d[2]['input'].append(10)),
 ('short_values',lambda d:d[2]['values'].pop()),
 ('short_names',lambda d:d[1]['variable_names'].pop()),
 ('natural_bool',lambda d:d[2]['values'].__setitem__(0,False)),
 ('natural_float',lambda d:d[2]['values'].__setitem__(0,0.0)),
 ('quartic_format',set_field(0,'format','other')),
 ('SOS_format',set_field(1,'format','other')),
 ('extra_quartic_field',set_field(0,'unexpected',0)),
 ('missing_witness_field',lambda d:d[2].pop('target')),
 ('nonstring_name',lambda d:d[1]['variable_names'].__setitem__(0,0)),
 ('coefficient_bool',lambda d:d[0]['terms'][0].__setitem__(0,True)),
 ('coefficient_float',lambda d:d[0]['terms'][0].__setitem__(0,float(d[0]['terms'][0][0]))),
 ('duplicate_quartic_term',lambda d:d[0]['terms'].append(copy.deepcopy(d[0]['terms'][0]))),
 ('index_bool',lambda d:d[0]['terms'].__setitem__(0,[1,[True]])),
 ('index_float',lambda d:d[0]['terms'].__setitem__(0,[1,[0.0]])),
])
passed=[]
for label,change in cases:
    data=copy.deepcopy(base);change(data)
    try:verify(*data,mutate=False)
    except ValidationError:passed.append(label)
    else:raise RuntimeError(('bad metadata accepted',label))
result=dict(status='PASS',optimized=not __debug__,negative_cases=len(passed),rejected_cases=passed,
            seconds=time.perf_counter()-start,verifier_sha256=hashlib.sha256((ROOT/'verify_example.py').read_bytes()).hexdigest())
(OUT/('example-validation-receipt-optimized.json'if not __debug__ else 'example-validation-receipt.json')).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:result[k]for k in('status','negative_cases','seconds')},sort_keys=True))
