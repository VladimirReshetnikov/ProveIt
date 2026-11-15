#!/usr/bin/env python3
"""Supplement the literal census with explicitly encoded JSON tables.

Uses the attributed QN/TDY recognizer in vendor/. No generator is executed.
"""
import argparse, hashlib, json, sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import json_recognizer as recognize
import census

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('incoming',type=Path)
    ap.add_argument('--output',type=Path,default=HERE/'json_supplement.json')
    args=ap.parse_args()
    known={c['canonical_class'] for c in json.loads((HERE/'frontier194.json').read_text())}
    found=[];errors=[];cache={};files=list(sorted(args.incoming.rglob('*.json')))
    for p in files:
        try:data=json.loads(p.read_text())
        except Exception as e:
            errors.append({'path':str(p.relative_to(args.incoming)),'error':str(e)});continue
        work=[('$',data)]
        while work:
            pointer,node=work.pop()
            decoded=recognize.decode(node)
            if decoded is not None:
                rows,states,halt=decoded
                if len(states)==194:
                    serial=''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(rows.items()))
                    h=hashlib.sha256(serial.encode()).hexdigest()
                    if h not in cache:
                        rr={(q,b):(w,int(d=='R'),n)for(q,b),(w,d,n)in rows.items()}
                        key=census.canonical(rr,states)
                        cache[h]=dict(canonical_class=census.tuple_digest(key)if key else None,
                                      spanning=key is not None)
                    found.append(dict(path=str(p.relative_to(args.incoming)),pointer=pointer,normalized_sha256=h,**cache[h]))
                continue
            if isinstance(node,dict):
                work.extend((pointer+'.'+str(k),v)for k,v in node.items() if isinstance(v,(dict,list,str)))
            elif isinstance(node,list):
                work.extend((pointer+'['+str(i)+']',v)for i,v in enumerate(node)if isinstance(v,(dict,list,str)))
    new=sorted({r['canonical_class']for r in found if r['spanning'] and r['canonical_class']not in known})
    result=dict(json_files=len(files),recognized194_occurrences=len(found),unique_normalized194=len(cache),
                additional_spanning194_classes=new,parse_errors=errors,occurrences=found,
                scope='Every JSON file in the five fully extracted incoming ZIPs, recursively recognizing explicit complete tables in the documented common formats; no arbitrary generator evaluation.')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='occurrences'},indent=2))
if __name__=='__main__':main()
