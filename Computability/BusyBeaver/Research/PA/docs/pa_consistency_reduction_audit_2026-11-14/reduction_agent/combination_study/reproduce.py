#!/usr/bin/env python3
"""Compose the two incoming AX grammars with MP-H and optional short negation.

This is an executable source/physical verification study, not an exported
PA proof, not a Lean certificate, and not a machine below 196 states.
"""
from pathlib import Path
import hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'inputs'))
import support as s
need=lambda x,msg: None if x else (_ for _ in ()).throw(ValueError(msg))

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def expanded(t):
 if isinstance(t,str):return expanded(s.c.raw_nodes()[t])
 if t[0]=='leaf':return t
 return tuple(expanded(x)for x in t)

def startup(rows,sites):
 q,h,ones=74,0,set()
 for step in range(58154):
  w,d,q=rows[q,int(h in ones)]
  (ones.add if w else ones.discard)(h);h+=1 if d else -1
 p=sites[25][0];want={h-1,h+48}|{h+i for i,b in enumerate(p)if b};pos=h+49
 for v in[0,0,0,0,0,0,2,0,0]+[1]*26:
  want.update(range(pos+1,pos+v+2));pos+=v+2
 need(q==84 and h==-2 and ones==want,'wrong exact startup frame')
 return {'steps':58154,'state':q,'head':h,'source_ordinal':25,'path':list(p),'all_cells_equal':True}

def main():
 need(__debug__ and not sys.flags.optimize,'run without Python -O')
 for rel,digest in json.loads((HERE/'INPUT_SHA256.json').read_text()).items():
  need(sha(HERE/rel)==digest,'pinned input changed: '+rel)
 pair=(s.INC,s.INC);s.c.MACROS[pair]=99;s.c.MACROS[(pair,pair)]=190
 s.c.MACROS.update({'node37':28,'node64':106})
 oldraw=s.c.raw_nodes
 s.c.raw_nodes=lambda:{**oldraw(),'node163':('node6','node147')}
 out=HERE/'results';out.mkdir(exist_ok=True);receipts=[]
 for family in ['diagonal','separate']:
  for neg in [False,True]:
   name=family+'_mp_h'+('_short_neg'if neg else '')
   t=s.c.read_grammar(HERE/'inputs'/f'{family}.grammar.json')
   if neg:t=s.repl(t,('node49',(s.INC,'node65')),('node37',(s.INC,'node64')))
   rows,idx,shape=s.c.build(t);rows[164,1]=(1,True,130)
   chosen=s.bestcompatible_all(rows,shape);table,aliases=s.apply(rows,chosen)
   ss,ins,cs=s.c.source(t);check=s.c.validate(table,cs)
   need(check['ok'],'failed symbolic contracts')
   boot=startup(table,ss)
   reach={74};todo=[74]
   for q in todo:
    for b in(0,1):
     z=table[q,b][2]
     if z!=254 and z not in reach:reach.add(z);todo.append(z)
   need(reach=={q for q,b in table},'unreachable supplied state')
   need(all(table[q,b]==s.c.machine()[0][q,b]for q in s.c.BOXSTATES for b in(0,1)),'boxed routine changed')
   labels=[74]+sorted(reach-{74})+[254];inv={q:i for i,q in enumerate(labels)}
   p=out/name;p.mkdir(exist_ok=True)
   native='#! start 74\n'+''.join(f'{q} {b} {w} {"R"if d else"L"} {z}\n'for(q,b),(w,d,z)in sorted(table.items()))
   dense=''.join(f'{inv[q]} {b} {w} {"R"if d else"L"} {inv[z]}\n'for(q,b),(w,d,z)in sorted(table.items(),key=lambda x:(inv[x[0][0]],x[0][1])))
   (p/'machine.native.tm').write_text(native);(p/'machine.tm').write_text(dense)
   (p/'labels.json').write_text(json.dumps(labels)+'\n');(p/'grammar.json').write_text(json.dumps(s.encode(t),indent=2)+'\n')
   (p/'folds.json').write_text(json.dumps(chosen,indent=2)+'\n')
   sites=[{'ordinal':i,'path':''.join(map(str,path)),'op':op,'arg':arg,'instruction':ins[i]}for i,(path,op,arg)in enumerate(ss)]
   (p/'sites.json').write_text(json.dumps(sites,indent=2)+'\n')
   receipt={'name':name,'states':len(reach),'rows':len(table),'source_sites':len(ss),'AX_reader_nodes':len(shape),'folds':len(chosen),'startup':boot,'symbolic':check,'native_sha256':sha(p/'machine.native.tm'),'dense_sha256':sha(p/'machine.tm'),'scope':'Executable whole-frame primitive contracts and exact finite startup only; inherited boxed register routines; no new arithmetic calibration or PA-internal equivalence proof.'}
   (p/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');receipts.append(receipt)
   print(json.dumps({k:v for k,v in receipt.items()if k!='startup'}),flush=True)
 (out/'receipt.json').write_text(json.dumps(receipts,indent=2)+'\n')
if __name__=='__main__':main()
