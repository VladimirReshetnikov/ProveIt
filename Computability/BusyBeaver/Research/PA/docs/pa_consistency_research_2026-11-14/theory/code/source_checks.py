# Extracted without changes from the supplied axioms/verify.py.
import compiler as c
from verify_emitter import require,literal_blocks,word

def source_binding(t,sites,ins):
 oldsites,oldins=c.program();oldblocks=literal_blocks();expected={}
 for op,a,b in oldblocks:
  expected.setdefault(op,(a,b))
 oldpaths={p:i for i,(p,op,arg)in enumerate(oldsites)};newpaths={p:i for i,(p,op,arg)in enumerate(sites)}
 prefix=(1,0,1,0,1,0,0,1)
 oldout=[s for s in oldsites if s[0][:8]!=prefix];newout=[s for s in sites if s[0][:8]!=prefix]
 require(oldout==newout,'exact unchanged exterior paths and operations');require(len(oldout)==169,'exterior count')
 def norm(code,start,end,ss):
  k=code[0]
  if k=='halt':return code
  narg=1 if k=='jump' else 2
  def dest(j):
   if start<=j<end:return('internal',j-start)
   if j==end:return('next',)
   return('external',ss[j][0])
  return tuple(code[:narg])+tuple(dest(j)for j in code[narg:])
 # Every macro is the same complete primitive/control block as upstream.
 cursor=50
 for op in word(t):
  a,b=expected[op];length=b-a
  for off in range(length):
   require(sites[cursor+off][1:]==oldsites[a+off][1:],'macro primitive identity')
   require(norm(ins[cursor+off],cursor,cursor+length,sites)==norm(oldins[a+off],a,b,oldsites),'macro relative control-flow identity')
  cursor+=length
 require(cursor-50==len(sites)-169,'all AX primitive sites bound')
 # Exterior targets can enter AX; compare their path names after re-association
 # only when both target sites lie outside AX. Entries into AX are its first site.
 for p,op,arg in newout:
  ni,oi=newpaths[p],oldpaths[p];nc,oc=ins[ni],oldins[oi];require(nc[:2] == oc[:2] if op in('inc','dec') else nc[:1]==oc[:1],'exterior opcode')
  narg=1 if nc[0]=='jump' else 2
  if nc[0]=='halt':continue
  for nn,oo in zip(nc[narg:],oc[narg:]):
   if oldsites[oo][0][:8]==prefix:require(oo==50 and nn==50,'AX entry binding')
   else:require(sites[nn][0]==oldsites[oo][0],'exterior successor binding')
 return {'macro_blocks':len(word(t)),'exterior_sites':169,'relative_control_flow_exact':True}
