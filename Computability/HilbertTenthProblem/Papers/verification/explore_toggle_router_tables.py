#!/usr/bin/env python3
"""Finite local-table checks; the separate note audits source interfaces."""
from pathlib import Path
import json
import hashlib


def verify():
    directions='NESW'
    ant=[]
    for old in range(2):
        for incoming in range(4):
            new_direction=(incoming+(1 if old==0 else -1))%4
            new_color=1-old
            c=1
            d=old*c
            e=(1-old)*c
            b=old^c
            assert c==d+e and old+e==b+d
            relative_turn=1 if e else -1
            assert new_color==b and new_direction==(incoming+relative_turn)%4
            ant.append(dict(old_color=old,incoming=directions[incoming],
                            new_color=new_color,outgoing=directions[new_direction]))
    assert len({(r['new_color'],r['outgoing']) for r in ant})==8
    table={
        ('H','n'):('V','w'),('H','e'):('H','w'),
        ('H','s'):('V','e'),('H','w'):('H','e'),
        ('V','n'):('V','s'),('V','e'):('H','n'),
        ('V','s'):('V','n'),('V','w'):('H','s'),
    }
    sides='nesw'
    for (state,input_side),observed in table.items():
        side=sides.index(input_side)
        horizontal_side=side%2==1
        parallel=horizontal_side==(state=='H')
        if parallel:
            expected=state,sides[(side+2)%4]
        else:
            expected=('V' if state=='H' else 'H'),sides[(side+3)%4]
        assert observed==expected
    assert len(set(table.values()))==8
    assert {table[state,'n'][0] for state in ('H','V')}=={'V'}
    assert len({1-state for state in (0,1)})==2
    pdf=Path('tmp/toggle_router_sources/morita2001.pdf')
    return dict(status='PASS_LOCAL_TABLES_ONLY',ant_rows=ant,
                rotary_rows=[dict(state=s,input=i,new_state=t,output=o)
                             for (s,i),(t,o) in table.items()],
                ant_active_toggle_match=True,rotary_active_toggle_match=False,
                morita_pdf_sha256=hashlib.sha256(pdf.read_bytes()).hexdigest() if pdf.exists() else None,
                primary_sources=[
                    'https://arxiv.org/pdf/nlin/0306022',
                    'https://arxiv.org/pdf/1702.05547',
                    'https://www.cs.auckland.ac.nz/~cristian/UMCreadings/revcomputCA.pdf'],
                proof='../1980/EXPLORATION_TOGGLE_ROUTER_UNIVERSALITY.md',
                scope='Exact finite transition-table checks. Primary-source background/input/halting contracts are audited in the note; no strong finite-blank universal walker or arithmetic saving is claimed.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
