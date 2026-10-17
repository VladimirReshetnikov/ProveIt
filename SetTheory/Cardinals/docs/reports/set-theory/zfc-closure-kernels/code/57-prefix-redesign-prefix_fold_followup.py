#!/usr/bin/env python3
"""Screen the other instructions for finite prefix-decrement fold survivors."""
from pathlib import Path
from collections import Counter
import json,time
import prefix_decrement as p
import permutation252_spare_fold_search as box

def main():
    began=time.monotonic();p.generate();p.m.audit.PERM=p.PERM
    guards=[g for g in p.m.guards() if not(g[1]=='CD' and g[2][1] is False)]
    samples=[c for c in box.samples() if c['op']!='decp']
    results=[]
    for path in sorted(p.HERE.glob('prefix-decrement-fold-*.tm')):
        table=p.m.audit.read_table(path.read_bytes())
        item=dict(table=path.name)
        for i,c in enumerate(samples):
            ok,reason,used,ticks=box.run(table,c,5000)
            if not ok:
                item['box']=dict(passed=False,samples_passed=i,reason=reason,case={k:v for k,v in c.items() if k not in ('ones','left','prefix')});break
        else:
            item['box']=dict(passed=True,samples_passed=len(samples))
            item['nonpositive_affine']=p.m.certify({(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in table.items()},guards)
            if item['nonpositive_affine']['passed']:print('FULL SURVIVOR',path.name,flush=True)
        results.append(item)
    result=dict(scope=__doc__,box_samples=len(samples),nonpositive_guards=len(guards),
                tables=len(results),results=results,total_seconds=time.monotonic()-began)
    (p.HERE/'prefix_fold_followup.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('results','scope')},indent=2))
    print('Passed boxes',sum(x['box']['passed'] for x in results),
          'passed nonpositive affine',sum(x.get('nonpositive_affine',{}).get('passed',False) for x in results),flush=True)

if __name__=='__main__':main()
