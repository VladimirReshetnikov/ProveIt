#!/usr/bin/env python3
"""Independent specialization audit; imports checker arithmetic, no producer."""
import argparse,hashlib,importlib.util,json,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def run():
    checker=module('inverse_lucas_free_port_checker',ROOT.parent/'verify.py')
    checker.check_source_pins()
    recipe=module('whole47_finite_coefficient_recipe',ROOT/'inherited'/'rebuild_coefficients.py')
    receipt={'coefficient_reconstruction':recipe.check_or_write(False),'circuits':[]}
    checker.ROOT=ROOT
    native=json.loads((ROOT/'inherited'/'q1_bv.json').read_text())['coefficient_binding']['ports']
    for weight in ('V2','bV'):
        path=ROOT/f'equation_{weight}.json';g=json.loads(path.read_text())
        parent=json.loads((ROOT.parent/path.name).read_text())
        checker.require(g['source']==parent['source'],'free-port graph differs')
        checker.require(g['coefficient_binding']['ports']==native,'mixed or changed whole47 tuple')
        checker.require(g['parent']['sha256']==hashlib.sha256((ROOT.parent/path.name).read_bytes()).hexdigest(),'free-port source pin')
        row={'file':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
             'operation_breakdown':checker.topology(g),'cuts':len(checker.exact_cuts(g)),
             'leading':checker.leading(g),'coefficients':checker.coefficients(g),
             'rejected_mutations':checker.mutations(g)}
        receipt['circuits'].append(row)
    receipt['raw_bytes']=sum((x['bits']+7)//8 for x in receipt['coefficient_reconstruction'])
    receipt['largest_port_bits']=max(x['bits'] for x in receipt['coefficient_reconstruction'])
    checker.require(receipt['raw_bytes']==207214 and receipt['largest_port_bits']==415904,'storage metrics')
    return receipt
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);a=ap.parse_args()
    result=run()
    if a.receipt:a.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'raw_bytes':result['raw_bytes'],'largest_port_bits':result['largest_port_bits'],
        'circuits':[{'file':r['file'],'degree':r['leading']['degree'],'operations':sum(r['operation_breakdown'].values()),'cuts':r['cuts'],'rejected_mutations':r['rejected_mutations']} for r in result['circuits']]},indent=2))
if __name__=='__main__':main()
