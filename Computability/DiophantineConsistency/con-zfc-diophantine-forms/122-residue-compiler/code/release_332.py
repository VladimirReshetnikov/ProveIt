#!/usr/bin/env python3
"""Produce and independently verify the selected 332-natural quartic.

Dependencies are local.  Put the frozen round14 architecture/intake tree
under ../vendor/round14 or set CONZFC_ROUND14_ROOT to its absolute path.
"""
from pathlib import Path
import argparse,json
from modular_factorial import generate_dominant
from check_independent import check as check_literal
from check_transform import check as check_macro,pell_digits

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--parent',type=Path,help='Optional frozen derived16_cantor directory for full semantic-prefix comparison')
    a=p.parse_args()
    counts=generate_dominant(a.output,'cantor',12)
    literal=check_literal(a.output,a.parent)
    macro={'literal_transform':check_macro(a.output),'finite_regressions':pell_digits()}
    (a.output/'INDEPENDENT_LITERAL_CHECK.json').write_text(json.dumps(literal,indent=2,sort_keys=True)+'\n')
    (a.output/'INDEPENDENT_TRANSFORM_CHECK.json').write_text(json.dumps(macro,indent=2,sort_keys=True)+'\n')
    summary={'counts':counts['natural'],'literal_status':literal['status'],
        'macro_status':macro['literal_transform']['status'],
        'regression_status':macro['finite_regressions']['status']}
    print(json.dumps(summary,indent=2))

if __name__=='__main__':
    main()
