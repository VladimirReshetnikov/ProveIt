#!/usr/bin/env python3
"""Combine existing exact Boolean/DNE AX changes with trace-ideal search.

Derived inputs retain the same 54 bootstrap interfaces and all 22 routes.
No trace output is represented as a literal machine certificate.
"""
from pathlib import Path
import argparse,json,hashlib,sys

def main():
 p=argparse.ArgumentParser();p.add_argument('--fine',type=Path,required=True);p.add_argument('--candidate',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 sys.path.insert(0,str(a.fine/'runtime/code'))
 from audit_fine_grammar import make_vocabulary,audit
 control=audit(a.candidate,short_scan=True)
 s,t,names,allowed,encode=make_vocabulary()
 g=json.loads(a.candidate.read_text()); override=g.get('source_override'); target=override['new_word'] if override else names[76]
 lines=(a.fine/'fine-grammar.txt').read_text().splitlines();nr,nroot,na=map(int,lines[0].split())
 old={w:(w[:int(k)],w[int(k):]) for k,w,_ in map(str.split,lines[1:nr+1])}
 allrules=dict(old);allrules.update({w:(l,r) for w,l,r in g['rules']})
 roots=[target if w==names[76] else w for w in lines[nr+1:nr+nroot+1]]
 text=[f'{len(allrules)} {len(roots)} {na}']+[f'{w} {l} {r}' for w,(l,r) in allrules.items()]+roots+lines[nr+nroot+1:]
 a.output.mkdir(parents=True,exist_ok=True)
 (a.output/'trace-grammar.txt').write_text('\n'.join(text)+'\n')
 constraints=(a.fine/'fine-constraints.txt').read_text().replace('W '+names[76]+'\n','W '+target+'\n')
 (a.output/'constraints.txt').write_text(constraints)
 (a.output/'locks.txt').write_bytes((a.fine/'fine-lock54.txt').read_bytes())
 res=[str(len(g['rules']))]+[' '.join(r) for r in g['rules']]+[str(len(g['routes']))]+[r['word'] for r in g['routes']]
 (a.output/'resume.txt').write_text('\n'.join(res)+'\n')
 # Derive footprints from the same pinned AST, not a handwritten matrix.
 from functools import cache
 @cache
 def bounds(i):
  r=s['ast_dag'][i]
  if r[0]=='L':
   op,*args=r[1];return (1,0) if op=='dec' else (args[0],0) if op=='brk' else (0,args[0]) if op=='cont' else (0,0)
  x,y=map(bounds,r[1:]);return max(x[0]-1,y[0],0),max(x[1],y[1]-1,0)
 @cache
 def fine(i):
  r=s['ast_dag'][i];return fine(r[1])+fine(r[2]) if r[0]=='N' and bounds(r[1])==bounds(r[2])==(0,0) else (i,)
 @cache
 def footprint(i):
  r=s['ast_dag'][i]
  if r[0]=='L':
   op,*args=r[1];return (1<<args[0] if op in ('inc','dec') else 0,op=='halt')
  x,y=map(footprint,r[1:]);return x[0]|y[0],x[1]or y[1]
 tokens=sorted({i for name in t.values() for i in fine(s['atoms'][name]['ast'])});alphabet='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';info={alphabet[j]:(i,*footprint(i)) for j,i in enumerate(tokens)}
 assert len(info)==30
 rows=[str(len(info))]+[f'{c} {m} {int(h)}' for c,(i,m,h) in info.items()]
 (a.output/'trace-info.txt').write_text('\n'.join(rows)+'\n')
 pairs=[(c,d) for c,(_,m,h) in info.items() for d,(_,m2,h2) in info.items() if c<d and not h and not h2 and not m&m2]
 (a.output/'pairs.txt').write_text(str(len(pairs))+'\n'+'\n'.join(f'{c} {d}' for c,d in pairs)+'\n')
 meta=dict(status='PREPARED_FROM_AUDITED_FINE_GRAMMAR',source_override=override,seed_candidate=str(a.candidate),seed_candidate_sha256=hashlib.sha256(a.candidate.read_bytes()).hexdigest(),control=control,independence_pairs=len(pairs),tokens={c:dict(ast=i,support_mask=m,has_halt=h) for c,(i,m,h) in info.items()},fine_path=str(a.fine.resolve()))
 (a.output/'input-provenance.json').write_text(json.dumps(meta,indent=2)+'\n')
 print(json.dumps(dict(output=str(a.output),rules=g['rules_count'],independence_pairs=len(pairs),AX_tokens=len(target))))
if __name__=='__main__':main()
