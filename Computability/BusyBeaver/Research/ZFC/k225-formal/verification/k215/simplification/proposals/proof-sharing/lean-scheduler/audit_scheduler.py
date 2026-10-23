#!/usr/bin/env python3
"""Reproduce the source-scope scheduler census from a pinned ProveIt checkout.

The result is declaration text size, not proof-term size, duplicate bytes that
can all be deleted, or a net-savings claim.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    args=ap.parse_args()
    root=args.repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
    rows=[]; sources={}
    for module in ('Enum254','Enum222','EnumDom','EnumPerm'):
        path=root/(module+'.lean');raw=path.read_bytes();text=raw.decode()
        sources[module]={'sha256':hashlib.sha256(raw).hexdigest(),
                         'bytes':len(raw),'lines':len(text.splitlines())}
        declarations=list(re.finditer(r'^(?:private\s+)?(?:theorem|def|abbrev|structure|inductive|macro)\b',text,re.M))
        for name in ('run_inv','run_add','drain','reach'):
            match=re.search(r'^theorem '+name+r'\b',text,re.M)
            if not match:raise SystemExit('Missing '+module+'.'+name)
            end=next((d.start() for d in declarations if d.start()>match.start()),len(text))
            body=text[match.start():end]
            # Remove the following declaration's documentation comment.
            comment=max(body.rfind('\n\n/-'),body.rfind('\n\n/--'))
            if comment>=0:body=body[:comment]
            body=body.rstrip()+'\n'
            rows.append({'module':module,'declaration':name,
                         'start_line':text[:match.start()].count('\n')+1,
                         'lines':len(body.splitlines()),'bytes':len(body.encode())})
    result={'basis_commit':'cbf94cb552a3b49509e0eee80e7455d4eb5974c6',
            'scope':'Source declaration/proof spans only; no net reduction claimed',
            'sources':sources,'declarations':rows,
            'total_lines':sum(r['lines'] for r in rows),
            'total_bytes':sum(r['bytes'] for r in rows)}
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(result['total_lines'],'lines,',result['total_bytes'],'bytes')

if __name__=='__main__':main()
