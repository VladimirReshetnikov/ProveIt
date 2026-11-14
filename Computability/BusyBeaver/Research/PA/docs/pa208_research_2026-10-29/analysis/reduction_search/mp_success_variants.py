#!/usr/bin/env python3
"""Build two three-primitive replacements of the closed MP success branch."""
from pathlib import Path
import sys,json
sys.dont_write_bytecode=True
sys.path.insert(0,'analysis/comparison')
import source_inventory as I
L=I.L
rows=json.loads((I.base/'machine/variant_plain/u208.sites.json').read_text())
root=L.tree(rows);g=L.graph_arithmetic(rows)[0]
assert g==L.graph_intervals(rows)
lo,hi=3847,3873
for tag,destination,success in [('cache_return',5,'(0,w,0,z)'),('current_move',1,'(z,w,0,0)')]:
    body=(('CD',4),(('CI',destination),('CC',2)))
    new=L.replace(root,'00110111',body);nr=L.sites(new)
    ng=L.graph_arithmetic(nr)[0];assert ng==L.graph_intervals(nr)
    delta=3-(hi-lo)
    assert nr[:lo]==rows[:lo]
    assert [(o,a) for _,o,a in nr[lo+3:]]==[(o,a) for _,o,a in rows[hi:]]
    for i,(effect,targets) in enumerate(g):
        if lo<=i<hi:continue
        index=i if i<lo else i+delta
        expected=[z if z<=lo else z+delta if z>=hi else None for z in targets]
        assert None not in expected,(i,targets)
        assert ng[index]==[effect,expected]
    out=Path('analysis/reduction_search')/tag;out.mkdir(exist_ok=True)
    (out/'source.sites.json').write_text(json.dumps(nr,separators=(',',':'))+'\n')
    (out/'source.sites.tsv').write_text(''.join(f'{p}\t{o}\t{a if a is not None else -1}\n' for p,o,a in nr))
    report={'variant':tag,'metrics':L.metrics(new),'replaced_old_interval':[lo,hi],
            'body_primitives':3,'two_CFG_resolvers_agree':True,'retained_CFG_check':True,
            'startup136_unchanged':nr[136]==rows[136],'success_postcondition':success,
            'literal_table_status':'Experimental source; no sub-208 table claimed'}
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))
