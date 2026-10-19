#!/usr/bin/env python3
"""Generate the coupled LM primitive / shortened negation source backend.

The only source DAG changes are node112: (57,42)->(40,42), and
node113: (112,78)->(112,77). Node112 has node113 as its sole parent.
The only changed framework route obligation is 218/0 prefix00: LNPQ->L.
"""
from pathlib import Path
from functools import cache
from collections import defaultdict
import argparse,json,sys,hashlib

def main():
 p=argparse.ArgumentParser();p.add_argument('--fine',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 sys.path.insert(0,str(a.fine/'runtime/code'))
 from audit_fine_grammar import make_vocabulary,TABLE
 source,oldterms,oldnames,oldallowed,encode=make_vocabulary();original=json.loads(json.dumps(source));ast=source['ast_dag']
 assert ast[112]==['N',57,42] and ast[113]==['N',112,78]
 assert [(i,r) for i,r in enumerate(ast) if r[0]=='N' and 112 in r[1:]]==[(113,['N',112,78])]
 ast[112]=['N',40,42];ast[113]=['N',112,77];source['rules']['237']=[218,124]
 @cache
 def bounds(i):
  r=ast[i]
  if r[0]=='L':
   op,*x=r[1];return (1,0) if op=='dec' else (x[0],0) if op=='brk' else (0,x[0]) if op=='cont' else (0,0)
  x,y=map(bounds,r[1:]);return max(x[0]-1,y[0],0),max(x[1],y[1]-1,0)
 @cache
 def fine(i):
  r=ast[i];return fine(r[1])+fine(r[2]) if r[0]=='N' and bounds(r[1])==bounds(r[2])==(0,0) else (i,)
 ids=sorted({i for name in oldterms.values() for i in fine(source['atoms'][name]['ast'])});alphabet='ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';tokens={i:alphabet[j] for j,i in enumerate(ids)}
 assert len(ids)==30
 word=lambda i:''.join(tokens[j] for j in fine(i))
 names={int(q):word(int(i)) for q,i in source['sequence_ast_roots'].items()};terms={word(source['atoms'][name]['ast']):name for name in oldterms.values()};allowed={word(source['atoms'][name]['ast']):oldallowed[oldw] for oldw,name in oldterms.items()}
 assert len(names)==127 and len(set(names.values()))==127 and len(terms)==44 and not set(names.values())&set(terms)
 assert names[237]=='LMPW' and 'LM' in terms and terms['LM']=='218:0'
 assert names[76]==oldnames[76].replace('LNPQMVQPW','LMPW')
 rules={names[q]:tuple(word(i) for i in ast[int(source['sequence_ast_roots'][str(q)])][1:]) for q in names}
 for w,(l,r) in rules.items():
  assert w==l+r
  for side,c in enumerate((l,r)):
   assert c in rules or c in terms,(w,c)
   if c in terms:assert allowed[c]&(1<<side)
 table={}
 for line in TABLE.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,t=line.split();table[int(q),int(b)]=(int(w),d,int(t))
 symbols=json.loads((a.fine/'runtime/inputs/semantic-symbols.json').read_text());inv={name:c for c,name in symbols.items()};oldwordtoname={w:q for q,w in oldnames.items()}
 def revise(oldword):
  if oldword in oldterms:
   return word(source['atoms'][oldterms[oldword]]['ast'])
  assert oldword in oldwordtoname,oldword
  return names[oldwordtoname[oldword]]
 groups={};route_derivation=[]
 for c in original['left_entry_projection_constraints']:
  r=c['reason'];key=(r['source'],r['read']);prefix=c['prefix'];oldtarget=encode(''.join(inv[t] for t in c['word']));target=revise(oldtarget)
  if r.get('via')==177:prefix=str(r['previous'])+prefix
  if key==(218,0) and prefix=='00':assert oldtarget=='LNPQ';target='L'
  groups.setdefault(key,[]).append((prefix,target));route_derivation.append(dict(source=key[0],read=key[1],prefix=prefix,old_target=oldtarget,new_target=target))
 # Start from existing literal source productions and choose exact transparent
 # routing contexts for the updated atomic source contracts.
 def project(w,bits):
  for bit in bits:
   if w not in rules:return None
   w=rules[w][int(bit)]
  return w
 routes={}
 for key,cs in groups.items():
  options=[w for w in rules if all(project(w,bits)==t for bits,t in cs)]
  if options:routes[key]=min(options,key=lambda w:(len(w),w));continue
  children=[]
  for side in (0,1):
   sub=[(b[1:],t) for b,t in cs if int(b[0])==side]
   opt=[w for w in set(rules)|set(terms) if all(project(w,bits)==t for bits,t in sub) and (w not in terms or allowed[w]&(1<<side))]
   assert opt,(key,side,sub)
   children.append(min(opt,key=lambda w:(len(w),w)))
  l,r=children;w=l+r;assert w not in terms
  if w in rules:assert rules[w]==(l,r)
  else:rules[w]=(l,r)
  routes[key]=w
 released={24,89,107,152,154,175,188,207,213,245};roots=[names[q] for q in source['required_entry_roots'] if q not in released]
 locks=[]
 for row in (a.fine/'fine-lock54.txt').read_text().splitlines()[1:]:
  w,b,t=row.split();nw,nt=revise(w),revise(t);assert nw==w and nt==t;locks.append((w,b,t));assert project(w,b)==t
 live=set()
 def visit(w):
  if w in terms or w in live:return
  assert w in rules;live.add(w)
  for c in rules[w]:visit(c)
 for w in roots+list(routes.values())+[w for w,b,t in locks]:visit(w)
 reduced={w:rules[w] for w in live}
 byast={int(i):names[int(q)] for q,i in source['sequence_ast_roots'].items()};exprs=[]
 @cache
 def expr(i):
  if i in byast:r=('W',byast[i])
  elif ast[i][0]=='L':r=('L',)
  else:r=('N',expr(ast[i][1]),expr(ast[i][2]))
  j=len(exprs);exprs.append(r);return j
 original_expr=expr(source['original_ast']);atom_expr={w:expr(source['atoms'][name]['ast']) for w,name in terms.items()}
 text=[str(len(groups))]
 for(src,read),cs in groups.items():
  text.append(f'{src} {read} {routes[src,read]} {len(cs)}');text +=[f'{b} {t}' for b,t in cs]
 text += [f'{len(exprs)} {original_expr} {len(terms)}']+[' '.join(map(str,r)) for r in exprs]+[f'{w} {j}' for w,j in atom_expr.items()]
 (a.output/'constraints.txt').write_text('\n'.join(text)+'\n')
 text=[f'{len(rules)} {len(roots)} {len(terms)}']+[f'{len(l)} {w} 0' for w,(l,r) in rules.items()]+roots+[f'{w} {m}' for w,m in allowed.items()]
 (a.output/'grammar.txt').write_text('\n'.join(text)+'\n')
 text=[str(len(reduced))]+[f'{len(l)} {w}' for w,(l,r) in reduced.items()]+[str(len(routes))]+list(routes.values());(a.output/'resume.txt').write_text('\n'.join(text)+'\n')
 (a.output/'locks.txt').write_text('54\n'+'\n'.join(' '.join(r) for r in locks)+'\n')
 data=dict(status='NEW_LM_BACKEND_SOURCE_ONLY',rules_count=len(reduced),erase177=True,retarget=-2,short_scan=True,properties=[],roots=roots,routes=[dict(source=src,read=read,word=w) for(src,read),w in routes.items()],rules=[[w,*reduced[w]] for w in sorted(reduced)],source_backend='lm-direct-negation')
 (a.output/'seed.json').write_text(json.dumps(data,indent=2)+'\n')
 mapping=dict(source=source,original_source=original,names=names,old_names=oldnames,terminals=terms,old_terminals=oldterms,allowed=allowed,token_to_ast={c:i for i,c in tokens.items()},route_derivation=route_derivation,roots=roots,source_edits=[dict(ast=112,old=[57,42],new=[40,42]),dict(ast=113,old=[112,78],new=[112,77])],fine_path=str(a.fine.resolve()),seed_rules=len(reduced))
 (a.output/'backend.json').write_text(json.dumps(mapping,indent=2)+'\n')
 print(json.dumps(dict(status='NEW_LM_BACKEND_INPUTS_PREPARED',source_states=127,rules=len(reduced),AX_tokens=len(names[76]),changed_routes=[r for r in route_derivation if r['old_target']!=r['new_target']],routes=[dict(source=k,word=v) for k,v in routes.items()])))
if __name__=='__main__':main()
