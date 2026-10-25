from pathlib import Path
import json
from collections import Counter
HERE=Path(__file__).resolve().parent
base=json.loads((HERE/'parents/P66.json').read_text())
# All retained rows through Nt, with first-square root omitted, first radicand added.
prefix=[]
for row in base['source']:
 if row[0] not in ['tau2','N0']: prefix.append(row)
 if row[0]=='first_product': prefix.append(['A','+','first_product',1])
 if row[0]=='Nt': break

def gen(mode):
 r=[v[:] for v in prefix]
 def add(n,op,x,y): r.append([n,op,x,y]);return n
 iA=add('iA','*','i','A')
 if mode=='triple':
  aa=add('aa','+','a',2)
  iAA=add('iAA','*',iA,aa)
  mult=add('mult','*',iAA,'main_root')
 else: mult=iA
 S=add('S','*',mult,'Dc2')
 I=add('I','*',mult,'c2')
 W=add('W','*',I,S)
 if mode=='triple': F2=add('f2','+',1,W)
 else:
  F2=add('f2','*','f','f')
  add('Ns','-',F2,W)
 if mode=='reduced':
  fm1=add('fm1','-',F2,1)
  Q=add('Q','*','Delta',fm1)
 else: Q=add('Q','*',S,S)
 cT=add('cT','*','c','T')
 inner=add('inner','-',cT,'R')
 V0=add('V0','*',F2,inner)
 V=add('V','-',V0,'c')
 V2=add('V2','*',V,V)
 G='A'
 if mode=='triple': G=add('G','*','A',F2)
 t2=add('t2','*','t','t')
 GV2=add('GV2','*',G,V2)
 diff=add('diff','-',t2,GV2)
 Qdiff=add('Qdiff','*',Q,diff)
 part=add('part','-',Qdiff,t2)
 E=add('Eprod','+',part,G)
 E3=add('E3','*',3,E)
 U=add('Eunit','+',E3,1)
 fac=['N1','Nk','Nt',U]+([] if mode=='triple' else ['Ns'])
 p=fac[0]
 for j,f in enumerate(fac[1:]):p=add('prod'+str(j),'*',p,f)
 add('output','-',p,1)
 witness=[x for x in base['witnesses'] if x not in ['tau','y']+(['f']if mode=='triple'else[])]+['t']
 obj={'name':'positive'+str(len(witness))+'_coprime_product_'+mode,'domain':'strictly positive integers','witnesses':witness,'fixed_numerals':base['fixed_numerals'],'source':r,'output':'output','operation_counts':dict(Counter(v[1]for v in r)),'operations':len(r),'parent':'whole indexed943 radix67 P66; pinned source e0c98c629bf10d30b695884f6b1d2ab361bdf513'}
 return obj
def root_saturated():
 d=gen('raw');r=d['source']
 start=next(j for j,x in enumerate(r)if x[0]=='iA');end=next(j for j,x in enumerate(r)if x[0]=='Q')+1
 block=[['I','*','i','c2'],['S0','*','i','Dc2'],['I_S0','*','I','S0'],['W','*','A','I_S0'],['f2','*','f','f'],['Ns','-','f2','W'],['Q','*','Delta','W']]
 d['source']=r[:start]+block+r[end:];d['name']='positive14_root_saturated_product';d['exact_degree']=189;d['operation_counts']=dict(Counter(x[1]for x in d['source']));d['operations']=len(d['source']);d['proof']='ROOT_SATURATION_PROOF.md'
 return d

def root_anchored():
 d=gen('triple');r=d['source']
 start=next(j for j,x in enumerate(r)if x[0]=='iA');end=next(j for j,x in enumerate(r)if x[0]=='Q')+1
 block=[['aa','+','a',2],['iAA','*','i','aa'],['mult','*','iAA','main_root'],['S0','*','mult','Dc2'],['I','*','mult','c2'],['W0','*','I','S0'],['W','*','A','W0'],['f2','+',1,'W'],['Q','*','Delta','W']]
 d['source']=r[:start]+block+r[end:];d['name']='positive13_root_anchored_product';d['exact_degree']=433;d['operation_counts']=dict(Counter(x[1]for x in d['source']));d['operations']=len(d['source']);d['proof']='ROOT_ANCHOR_PROOF.md'
 return d

def main():
 import argparse
 parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');args=parser.parse_args()
 for d in (root_saturated(),gen('reduced'),root_anchored()):
  files={'positive14_root_saturated_product':'equation_14_raw.json','positive14_coprime_product_reduced':'equation_14_reduced.json','positive13_root_anchored_product':'equation_13_anchored.json'}
  path=HERE/files[d['name']];payload=json.dumps(d,indent=2)+'\n'
  if args.check:
   if path.read_text()!=payload:raise ValueError('rebuild mismatch: '+path.name)
  else:path.write_text(payload)
  print(path.name+': '+str(d['operations'])+' operations')
if __name__=='__main__':main()
