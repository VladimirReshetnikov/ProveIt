"""Independent full polynomial-row verification of the rank-one factor lift."""
import json,hashlib,argparse
from pathlib import Path
from audit_height_one import require,poly,subst,add

def verify(old,new,c):
 nv=len(old['variables']);nn=len(new['variables']);off=c['row_offset'];require(c['original_variables']==nv and off==c['definition_rows']==nn-nv,'dimensions')
 require(new['domain']==old['domain']=='unrestricted integers','domains');require(new['variables'][:nv]==old['variables'],'old coordinates preserved');require(len(new['residuals'])==len(old['residuals'])+off,'row count')
 ss=[{(i,):1} for i in range(nv)];defs={}
 for k,r in enumerate(new['residuals'][:off]):
  pivot=nv+k;p=poly(r['terms']);require(p.get((pivot,))==1 and all(pivot not in m or m==(pivot,) for m in p),'monic new coordinate')
  rest=add(p,{(pivot,):1},-1);require(all(len(m)<=1 and all(i<nv for i in m) for m in rest),'affine original-only definition')
  value={m:-coef for m,coef in rest.items()};ss.append(value);defs[pivot]=value
 for a,b in zip(old['residuals'],new['residuals'][off:]):
  require(a['label']==b['label'],'row label preserved');require(poly(a['terms'])==subst(poly(b['terms']),ss),'complete exact source row pullback')
 seen=set()
 for rec in c['records']:
  i=rec['source_row'];require(i not in seen and 0<=i<len(old['residuals']),'record row');seen.add(i);p=rec['pivot'];require(p in defs and poly(rec['affine'])==defs[p],'record affine map');require(rec['sign'] in (-1,1),'square sign')
 # Every changed row is accounted for, no reliance on a search heuristic.
 for i,(a,b) in enumerate(zip(old['residuals'],new['residuals'][off:])):
  if a!=b:require(i in seen,'unrecorded row change')
 require({r['pivot'] for r in c['records']}==set(defs),'all affine variables used')
 return {'status':'pass','source_variables':nv,'lifted_variables':nn,'source_rows':len(old['residuals']),'lifted_rows':len(new['residuals']),'affine_definitions':off,'refactored_rows':len(seen),'identity':'Q(A(x))=P_source(x), all constructor rows vanish; unique affine extension; original coordinates fixed','scope':'Universal exact row identities and complete inverse. No source consistency theorem is re-proved.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--source',required=True,type=Path);p.add_argument('--factor-dir',required=True,type=Path);p.add_argument('--output',required=True,type=Path);a=p.parse_args();b=a.source.read_bytes();new=(a.factor_dir/'source.json').read_bytes();cb=(a.factor_dir/'factor_certificate.json').read_bytes();c=json.loads(cb);require(c['source_sha256']==hashlib.sha256(b).hexdigest(),'original digest');r=verify(json.loads(b),json.loads(new),c);r.update(source_sha256=hashlib.sha256(b).hexdigest(),factored_source_sha256=hashlib.sha256(new).hexdigest(),certificate_sha256=hashlib.sha256(cb).hexdigest());a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
