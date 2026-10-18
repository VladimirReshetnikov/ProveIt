#!/usr/bin/env python3
"""Match root's exact frozen macro support and two-incoming eligibility."""
import json
import fold_search as f

def main():
    protected=set()
    def visit(value):
        if isinstance(value,dict):
            if value.get('rule') in ('literal','unary-induction'):
                protected.add((value['state'],value['read']))
            for child in value.values():visit(child)
        elif isinstance(value,list):
            for child in value:visit(child)
    visit(json.loads((f.BASE/'results/macro-inductions.json').read_text()))
    keep={q for q,b in protected}|{f.OLD[k][2] for k in protected}|{96,95}
    family=[]
    for q in f.STATES:
        if q in keep:continue
        incoming=[k for k,row in f.OLD.items() if row[2]==q and k[0]!=q]
        if len(incoming)==2 and not any(k in protected for k in incoming):
            family.append((q,incoming))
    (f.ROOT/'twoaction-states.txt').write_text(str(len(family))+'\n'+''.join(
        f'{q} {inc[0][0]} {inc[0][1]} {inc[1][0]} {inc[1][1]}\n' for q,inc in family))
    (f.ROOT/'twoaction-eligibility.json').write_text(json.dumps(dict(protected_pairs=sorted(protected),protected_states=sorted(keep),eligible=family),indent=2)+'\n')
    print('protected',len(protected),'states',len(family),[q for q,_ in family])

if __name__=='__main__':main()
