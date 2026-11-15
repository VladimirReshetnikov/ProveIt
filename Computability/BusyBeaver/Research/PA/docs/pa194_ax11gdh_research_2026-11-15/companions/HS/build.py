#!/usr/bin/env python3
"""Rebuild PA194AX11GDHS from exact inherited inputs and five word substitutions.

All dependencies are local. The inherited compiler and physical checker are
attributed in NOTICE.md. This builder's assertions establish construction
identities, not by themselves the absolute iPRA calibration.
"""
from pathlib import Path
import argparse,json,hashlib,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'compiler'))
import compiler as c
import support as s
INC=('leaf','inc',1);BREAK=('leaf','breakTo',1)
EXPECTED='2d5b61572ee6e7dd19e23d7e10181c2f28410cddf0970fd145211c88ebca44cc'
def sha(x):return hashlib.sha256(x).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def tuples(x):return tuple(map(tuples,x))if isinstance(x,list)else{k:tuples(v)for k,v in x.items()}if isinstance(x,dict)else x
def normalize(t):
 if t=='node60':return INC,INC
 if t=='node61':return(INC,INC),(INC,INC)
 return tuple(map(normalize,t))if c.isnode(t)else t
def word(t):return word(t[0])+word(t[1])if c.isnode(t)else[t]
def substitute(t,w):
 stream=iter(w)
 def rec(t):return tuple(map(rec,t))if c.isnode(t)else next(stream)
 out=rec(t);assert next(stream,None)is None;return out
def encoded(t):
 rules={};ids={}
 def rec(t):
  if not c.isnode(t):return t
  if t in ids:return ids[t]
  k='g'+str(len(ids));ids[t]=k;rules[k]=[rec(z)for z in t];return k
 return {'root':rec(t),'rules':rules}
def construct(out,full=True):
 assert __debug__,'Assertions required; do not run Python -O'
 for f,h in json.loads((HERE/'INPUT_SHA256.json').read_text()).items():assert sha((HERE/f).read_bytes())==h,(f,'input changed')
 primary=normalize(c.read_grammar(HERE/'inputs/primary.grammar.json'))
 diagonal=normalize(c.read_grammar(HERE/'inputs/diagonal_D.grammar.json'))
 pw,dw=word(primary),word(diagonal);assert len(pw)==len(dw)==190
 assert[(i,a,b)for i,(a,b)in enumerate(zip(pw,dw))if a!=b]==[(121,'node70','node55'),(122,'node70','node55'),(123,'node70','node55'),(189,BREAK,('leaf','dec',4))]
 dw[1]='node70';dw[-1]='node49'
 changes=[(i,a,b)for i,(a,b)in enumerate(zip(pw,dw))if a!=b]
 assert changes==[(1,'node55','node70'),(121,'node70','node55'),(122,'node70','node55'),(123,'node70','node55'),(189,BREAK,'node49')]
 tree= substitute(diagonal,dw);reference=substitute(primary,dw)
 rows=s.read_table(HERE/'inputs/base.raw.native.tm');nodes=tuples(json.loads((HERE/'inputs/base.nodes.json').read_text()))
 c.machine=lambda:(rows,[]);c.raw_nodes=lambda:nodes
 c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
 raw,_,shape=c.build(tree);assert len(raw)//2==204 and len(shape)==69
 sites,ins,contracts=c.source(tree);_,refins,_=c.source(reference);assert ins==refins
 folds=json.loads((HERE/'inputs/folds.json').read_text());child,aliases=s.apply_folds(raw,folds)
 local=s.check_local_folds(raw,child,aliases,folds);assert len(folds)==10 and len(local['cases'])==40
 assert len(child)==388 and all(child[q,b]==rows[q,b]for q in c.BOXSTATES for b in(0,1))
 startup=s.startup(child,sites[25][0]);assert startup['steps']==57768
 dense,labels=s.dense_table(child,194);assert sha(s.table_text(dense).encode())==EXPECTED
 runtime=c.validate(child,contracts)if full else None
 assert not full or runtime['ok']
 out.mkdir(parents=True,exist_ok=True)
 for name,t in [('machine.tm',dense),('machine.native.tm',child),('raw.native.tm',raw)]: (out/name).write_text(s.table_text(t))
 for name,x in [('nodes.json',nodes),('grammar.json',encoded(tree)),('reference_grammar.json',encoded(reference)),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',ins),('folds.json',folds),('labels.json',labels),('local_cases.json',local)]:dump(out/name,x)
 receipt={'name':'PA194AX11GDHS','states':194,'rows':388,'start':0,'halt':194,'native_start':74,'native_halt':254,'raw_states':204,'fixed_controls':135,'AX_readers':69,'simultaneous_folds':10,'source_sites':len(sites),'source_outcomes':len(contracts),'source_word_changes_from_primary':changes,'all_resolved_source_instructions_match_reference':True,'arithmetic_boxes_unchanged':True,'startup':startup,'symbolic_validation':runtime,'sha256':EXPECTED,'native_sha256':sha(s.table_text(child).encode())}
 dump(out/'receipt.json',receipt)
 print(json.dumps({k:receipt[k]for k in ['name','states','raw_states','AX_readers','simultaneous_folds','source_sites','source_outcomes','sha256']}),flush=True)
 return receipt
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);p.add_argument('--quick',action='store_true');a=p.parse_args();construct(a.output,not a.quick)
