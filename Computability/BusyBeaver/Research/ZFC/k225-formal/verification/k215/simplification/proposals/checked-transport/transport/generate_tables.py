#!/usr/bin/env python3
"""Reproduce/audit the two literal Coq table lists; no proof compiler required."""
from pathlib import Path
import argparse, hashlib, json, re
ROOT = Path(__file__).resolve().parent
EXPECTED = {
    'old.tm':'9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2',
    'new.tm':'da20914ad9bda3f75de0381f2c05a7b5e67d26199b57b870a5ea3b72511ab627',
}
def need(p, message):
    if not p: raise ValueError(message)
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def parse_native(p):
    rows=[]
    for line in p.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'): continue
        q,b,w,d,z=line.split(); rows.append((int(q),int(b),int(w),d,int(z)))
    return rows

def parse_literal(file, definition):
    s=file.read_text()
    body=re.search(r'Definition '+re.escape(definition)+r'\s*:\s*list entry\s*:=\s*\[(.*?)\]\.',s,re.S)
    need(body is not None, 'missing Coq literal '+definition)
    matches=re.findall(r'E\s+(\d+)\s+(true|false)\s+\(A\s+(true|false)\s+([LR])\s+(\d+)\)',body.group(1))
    rows=[(int(q),int(b=='true'),int(w=='true'),d,int(z)) for q,b,w,d,z in matches]
    return rows

def emit(rows, name):
    bits=['false','true']
    lines=[f' E {q} {bits[b]} (A {bits[w]} {d} {z})' for q,b,w,d,z in rows]
    return f'Definition {name} : list entry := [\n'+';\n'.join(lines)+'\n].\n'

def audit():
    old=parse_native(ROOT/'old.tm');new=parse_native(ROOT/'new.tm')
    for f,h in EXPECTED.items():need(digest(ROOT/f)==h,'native hash '+f)
    need(old==parse_literal(ROOT/'NativeContext.v','old_rows'),'old literal mismatch')
    need(new==parse_literal(ROOT/'LiteralBindings.v','new_literal_rows'),'new literal mismatch')
    labels={q for q,b,w,d,z in old}; need(len(labels)==215,'working count')
    need({q for q,b,w,d,z in new}==labels,'working labels changed')
    for name,rows in [('old',old),('new',new)]:
        need(len(rows)==430 and len({(q,b) for q,b,w,d,z in rows})==430,name+' complete binary rows')
        need({(q,b) for q,b,w,d,z in rows}=={(q,b) for q in labels for b in [0,1]},name+' domain')
        need(all(z==254 or z in labels for q,b,w,d,z in rows),name+' dangling target')
        need(254 not in labels and 0 in labels,name+' terminal/start')
    changes=[{'row':[a[0],a[1]],'old':list(a[2:]),'new':list(z[2:])} for a,z in zip(old,new) if a!=z]
    expected={(13,1):81,(27,1):302,(83,1):57,(156,1):52,(198,0):54}
    need(len(changes)==5 and {(c['row'][0],c['row'][1]):c['new'][2] for c in changes}==expected,'patch rows')
    need(all(a[:4]==z[:4] for a,z in zip(old,new)),'non-retargeting change')
    critical={13,27,38,42,83,156,198}
    incoming=[(q,b,z) for q,b,w,d,z in old if z in critical]
    need(incoming==[(8,1,13),(26,1,38),(28,1,42),(38,0,13),(42,0,13),(66,0,198),(73,1,83),(83,1,42),(95,0,27),(109,1,42),(189,1,156)],'critical incoming slice')
    return {'status':'PASS','working_states':215,'rows_each':430,'start':0,'halt':254,
            'native_sha256':EXPECTED,'changes':changes,'critical_incoming_rows':incoming,
            'proof_sources_sha256':{f:digest(ROOT/f) for f in ['NativeContext.v','LiteralBindings.v']},
            'scope':'Literal-byte/list audit; formal theorem verification is a separate Coq build.'}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check',action='store_true');p.add_argument('--output',type=Path)
    p.add_argument('--table',choices=['old','new'],default='old')
    a=p.parse_args()
    if a.check:
        r=audit();s=json.dumps(r,indent=2)+'\n'
        if a.output: a.output.write_text(s)
        print(s,end='')
    else:
        print(emit(parse_native(ROOT/(a.table+'.tm')),'old_rows' if a.table=='old' else 'new_literal_rows'),end='')
if __name__=='__main__':main()
