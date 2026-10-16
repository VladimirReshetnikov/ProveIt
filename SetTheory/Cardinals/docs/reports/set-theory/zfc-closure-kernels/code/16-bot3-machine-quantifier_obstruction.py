"""An identity-quantifier counterinterpretation to generic FOL completeness.

This applies to the reduced logical skeleton, including same-variable
specialization.  It makes no claim that the C/G or PSC theory rows hold.
"""
from __future__ import annotations

import argparse
from itertools import product
import json
from pathlib import Path


def imp(a,b):
    return not a or b


def check():
    # Q_i is identity for every variable i; F is genuine false. Generalization
    # and modus ponens therefore preserve validity. A predicate atom can have
    # any Boolean value independently of all differently labelled atoms.
    checks={}
    checks["rho8_valuations"]=sum(
        imp(imp(imp(c,u),a),imp(imp(a,c),imp(b,c)))
        for a,b,c,u in product((False,True),repeat=4))
    assert checks["rho8_valuations"]==16
    for a,b,c in product((False,True),repeat=3):
        F=False
        neg=lambda x:imp(x,F)
        quant=lambda x:x
        exists=lambda x:neg(quant(neg(x)))
        assert imp(exists(quant(b)),b) # original rho6
        assert imp(b,quant(exists(b))) # dual rho6, optional here
        assert imp(quant(imp(b,c)),imp(quant(b),quant(c))) # distribution
        assert imp(quant(quant(c)),quant(quant(c))) # commutation
        assert imp(a,quant(a)) # atomic vacuity, even without a freshness gate
        assert imp(quant(b),b) # same-variable specialization
        assert imp(F,b) # explicit explosion also holds
    checks["quantifier_row_payload_cases"]=8
    atom={(0,0):False,(0,1):True,(2,1):False}
    universal_x_Rxy=atom[0,1] # Q_0 is identity.
    substituted_Rzy=atom[2,1]
    target=imp(universal_x_Rxy,substituted_Rzy)
    assert not target
    return {
        "interpretation":{"Bottom":False,"Truth":True,
                          "Imp":"material implication","All_i":"identity for every i",
                          "Rel_0_0":False,"Rel_0_1":True,"Rel_2_1":False},
        "validated_rows":["rho8","original_rho6","dual_rho6","distribution",
                          "commutation","atomic_vacuity","same_variable_specialization",
                          "explosion"],
        "rule_preservation":{"modus_ponens":True,"generalization":True},
        "finite_checks":checks,
        "ordinary_FOL_valid_but_counterinterpretation_false":"(All 0 (Rel 0 1)) -> Rel 2 1",
        "counterexample_value":target,
        "conclusion":"This reduced logic, even with same-variable specialization and EFQ, cannot derive every ordinary equality-free first-order validity.",
        "scope":"No claim is made that additional PSC or C/G theory rows are valid in this algebra. It is a generic logical-completeness obstruction, not a theory inconsistency or machine-nonhalting theorem.",
    }


if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("run without -O")
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path)
    args=ap.parse_args()
    text=json.dumps(check(),indent=2,sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(text)
    print(text,end="")
