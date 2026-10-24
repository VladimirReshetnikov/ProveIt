"""Build the complete improved direct consistency quartic and certificates."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import base_builder
from power_builder import PowerBuilder
from shared_power_builder import SharedPowerBuilder
from compress import compress,expand,terms


def write(path,obj):
    data=(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()
    path.write_bytes(data)
    return sha256(data).hexdigest()


def census(eq,p):
    return {'variables':len(eq['variables']),'quadratic_rows':len(eq['residuals']),
            'exact_degree':max(len(m) for m in p),'expanded_monomials':len(p),
            'max_abs_row_coefficient':max(abs(c) for r in eq['residuals'] for c,m in r['terms']),
            'max_abs_expanded_coefficient':max(map(abs,p.values())),
            'variable_kinds':dict(Counter(v['kind'] for v in eq['variables']))}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).parent/'output')
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    here=Path(__file__).parent
    data=(here/'wire_eliminated_source.json').read_bytes()
    source=json.loads(data)
    base_builder.Builder=SharedPowerBuilder
    b=base_builder.construct(source)
    b.finalize()
    raw={'variables':b.variables,'rows':b.rows,'macro_log':b.macro_log,
         'power_arguments':b.power_arguments,'shared_pell':b.shared_pell,
         'powers':[{'base':n,'exponent':k,'output':m} for (n,k),m in b.powers.items()],
         'pell_indices':[{'exponent':k,'X':xy[0],'Y':xy[1]} for k,xy in b.pell_indices.items()]}
    parent,_,metrics=b.export(sha256(data).hexdigest(),'cofinal11_power16')
    output,trace=compress(parent)
    p=expand(output)
    final_metrics=census(output,p)
    output['metrics']=final_metrics
    hashes={}
    for name,obj in [('raw_builder.json',raw),('before_terminal.json',parent),('equation.json',output),
                     ('elimination_trace.json',trace),('envelope_certificate.json',b.envelope_certificate),
                     ('expanded_polynomial.json',{'schema':'sparse_integer_polynomial_v1',
                      'domain':'nonnegative integers','variables':len(output['variables']),'terms':terms(p)})]:
        hashes[name]=write(args.output/name,obj)
    receipt={'status':'BUILT','before_terminal':metrics,'after_terminal':final_metrics,
             'eliminated_terminal_variables':len(trace['steps']),
             'power_graphs':len(b.powers),'binomial_graphs':len(b.binomials),'factorial_graphs':len(b.factorials),
             'shared_pell_index_certificates':len(b.pell_indices),
             'sha256':hashes,'source_sha256':sha256(data).hexdigest(),
             'code_sha256':{p.name:sha256(p.read_bytes()).hexdigest() for p in here.glob('*.py')},
             'scope':'Exact finite construction; ordinary semantic proof is in the report.'}
    (args.output/'BUILD.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))


if __name__=='__main__':main()
