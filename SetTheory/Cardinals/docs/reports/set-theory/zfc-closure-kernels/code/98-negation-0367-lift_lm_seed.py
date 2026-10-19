#!/usr/bin/env python3
"""Lift an exact original-source 128-rule grammar through the LM source edit."""
from pathlib import Path
import argparse,json

def main():
 p=argparse.ArgumentParser();p.add_argument('--backend',type=Path,required=True);p.add_argument('--seed',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 b=json.loads((a.backend/'backend.json').read_text());g=json.loads(a.seed.read_text());assert not g.get('source_override') or b.get('source_override',{}).get('inherited_fine_override')==g['source_override']
 f=lambda w:w.replace('LNPQMVQPW','LMPW').replace('LNPQM','LM')
 rules={};fixed=[];collapsed=[];terms=b['terminals'];allowed=b['allowed']
 images={f(w) for w,l,r in g['rules']}|set(terms)
 for w,l,r in g['rules']:
  nw,nl,nr=map(f,(w,l,r))
  if nw in terms:
   collapsed.append(dict(old=w,image=nw,kind='terminal'));continue
  if nw!=nl+nr:
   opts=[(nw[:k],nw[k:]) for k in range(1,len(nw)) if nw[:k] in images and nw[k:] in images and (nw[:k] not in terms or allowed[nw[:k]]&1) and (nw[k:] not in terms or allowed[nw[k:]]&2)]
   if not opts:
    repairs=[]
    for i in range(1,len(nw)):
     for j in range(i+1,len(nw)):
      x,y,z=nw[:i],nw[i:j],nw[j:]
      if not all(c in images for c in (x,y,z)):continue
      for right in (False,True):
       p1,p2=(y,z) if right else (x,y);part=p1+p2
       top=(x,part) if right else (part,z)
       if all(c not in terms or allowed[c]&(1<<side) for pair in ((p1,p2),top) for side,c in enumerate(pair)):
        repairs.append((max(map(len,top)),part,p1,p2,top))
    assert repairs,('Unrealized contraction boundary',w,l,r,nw)
    _,part,p1,p2,top=min(repairs);assert part not in images;rules[part]=(p1,p2);images.add(part);opts=[top]
   nl,nr=min(opts,key=lambda lr:(max(map(len,lr)),len(lr[0]),lr));fixed.append(w)
  assert nw==nl+nr
  if nw in rules:collapsed.append(dict(old=w,image=nw,kind='duplicate'))
  else:rules[nw]=(nl,nr)
 routes={(r['source'],r['read']):f(r['word']) for r in g['routes']}

 def project(w,bits):
  for bit in bits:
   if w not in rules:return None
   w=rules[w][int(bit)]
  return w
 groups={}
 for r in b['route_derivation']:groups.setdefault((r['source'],r['read']),[]).append((r['prefix'],r['new_target']))
 for key,cs in groups.items():
  if all(project(routes[key],bits)==t for bits,t in cs):continue
  opts=[w for w in rules if all(project(w,bits)==t for bits,t in cs)]
  if opts:routes[key]=min(opts,key=lambda w:(len(w),w));continue
  child=[]
  for side in (0,1):
   sub=[(bits[1:],t) for bits,t in cs if int(bits[0])==side]
   opts=[w for w in set(rules)|set(terms) if all(project(w,bits)==t for bits,t in sub) and (w not in terms or allowed[w]&(1<<side))]
   assert opts,(key,side,sub);child.append(min(opts,key=lambda w:(len(w),w)))
  l,r=child;w=l+r
  assert w not in terms
  if w in rules:assert rules[w]==(l,r)
  else:rules[w]=(l,r)
  routes[key]=w
 roots=b['roots'];locks=(a.backend/'locks.txt').read_text().splitlines();live=set()
 def visit(w):
  if w in terms or w in live:return
  live.add(w)
  for c in rules[w]:visit(c)
 for w in roots+list(routes.values())+[r.split()[0] for r in locks[1:]]:visit(w)
 reduced={w:rules[w] for w in live}
 out=dict(g,status='LM_SOURCE_GRAMMAR_PROPOSAL',rules_count=len(reduced),roots=roots,rules=[[w,*reduced[w]] for w in sorted(reduced)],routes=[dict(source=k[0],read=k[1],word=w) for k,w in routes.items()],properties=[],short_scan=True,source_backend='lm-direct-negation')
 (a.output/'seed.json').write_text(json.dumps(out,indent=2)+'\n')
 text=[str(len(reduced))]+[f'{len(l)} {w}' for w,(l,r) in reduced.items()]+[str(len(routes))]+list(routes.values());(a.output/'resume.txt').write_text('\n'.join(text)+'\n')
 for name in ('grammar.txt','constraints.txt','locks.txt'):(a.output/name).write_bytes((a.backend/name).read_bytes())
 print(json.dumps(dict(status='LIFTED',source_rules=g['rules_count'],initial_lift_rules=len(rules),live_rules=len(reduced),nonhomomorphic_joins_reparsed=fixed,collapsed_images=collapsed,new_route218=routes[218,0])))
if __name__=='__main__':main()
