#!/usr/bin/env python3
"""Freeze the candidate list, then make a single pseudorandom selection."""
import hashlib, json, random, secrets
from pathlib import Path

root=Path(__file__).resolve().parent
candidates=[
 {'id':'A225114','subject':'Skew partitions with no empty rows or columns','conjecturer':'Mikhail Kurkov','conjecture_date':'2024-09-03','formula':'A(x)=1/(2-C(x)), C(x)=1/(1-x/(1-x/(1-x^2/(1-x^2/(1-x^3/(1-x^3/(...)))))))','url':'https://oeis.org/A225114'},
 {'id':'A244475','subject':"Fifth-largest distinct value in a row of Stern\u2019s diatomic triangle",'conjecturer':'Alois P. Heinz','conjecture_date':'2022-06-20','formula':'-x^3*(x^14+x^13+x^12+2*x^11+3*x^10+5*x^9+8*x^8+x^7+3*x^6+3*x^5+2*x^4+4*x^3+5*x^2+2*x+1)/(x^2+x-1)','url':'https://oeis.org/A244475'},
 {'id':'A381190','subject':'Connected minimal dominating sets of n-trapezohedral graphs','conjecturer':'Joerg Arndt','conjecture_date':'2026-01-07','formula':'-2*x^3*(4*x^5+8*x^4+4*x^3-9*x^2-8*x-3)/(x^3+x^2-1)^2','url':'https://oeis.org/A381190'},
 {'id':'A391632','subject':'Mutual-visibility sets of n-Andrasfai graphs','conjecturer':'Andrew Howroyd','conjecture_date':'2026-01-12','formula':'x*(4-19*x+33*x^2-40*x^3+8*x^4)/(1-10*x+29*x^2-32*x^3+8*x^4)','url':'https://oeis.org/A391632'}
]
if (root/'selection.json').exists():
    raise SystemExit('Selection already recorded; refusing to redraw.')
text=json.dumps(candidates,indent=2,ensure_ascii=False)+'\n'
(root/'candidates.json').write_text(text)
seed=secrets.randbits(128)
i=random.Random(seed).randrange(len(candidates))
record={'method':'Python random.Random(seed).randrange(4); seed from secrets.randbits(128)', 'seed_decimal':str(seed),'candidate_list_sha256':hashlib.sha256(text.encode()).hexdigest(),'zero_based_index':i,'selected_id':candidates[i]['id'],'draw_count':1}
(root/'selection.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
