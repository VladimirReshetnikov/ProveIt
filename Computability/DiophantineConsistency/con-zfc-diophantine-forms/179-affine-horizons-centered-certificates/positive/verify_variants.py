#!/usr/bin/env python3
"""Independent exact graph/degree/tuple checks for the plus-one center."""
from pathlib import Path
import argparse,hashlib,json,sys
sys.dont_write_bytecode=True
import verify as v
ROOT=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);a=ap.parse_args();out=[]
    for directory in (ROOT,ROOT/'start_marker4177'):
        v.ROOT=directory;p=directory/'equation_plus1_bV.json';g=json.loads(p.read_text())
        parent=directory/g['parent']['path'];v.require(hashlib.sha256(parent.read_bytes()).hexdigest()==g['parent']['sha256'],'parent graph pin')
        out.append({'file':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
          'operations':g['operations'],'breakdown':v.topology(g),'cuts':v.exact_cuts(g),
          'algebraic_identities':v.algebra(),'leading':v.leading(g),'coefficients':v.coefficients(g),
          'rejected_mutations':v.mutations(g)})
    result={'variants':out,'scope':'Exact finite graph checks; full tuple/native/Pcs reconstruction is separately replayed by reproduce.sh.'}
    if a.receipt:a.receipt.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps([{'file':x['file'],'operations':x['operations'],'degree':x['leading']['degree'],'cuts':len(x['cuts']),'rejected_mutations':x['rejected_mutations']} for x in out],indent=2))
if __name__=='__main__':main()
