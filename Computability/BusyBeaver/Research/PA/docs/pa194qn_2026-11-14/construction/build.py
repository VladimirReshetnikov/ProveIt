#!/usr/bin/env python3
"""Candidate QN5, QN6, QH5: explicit crossed sources and complete tape checks.
The compiler, source language and symbolic semantics retain their upstream
attribution. This is an executable certificate, not a proof-assistant theorem.
"""
from pathlib import Path
import sys,json,hashlib,argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c,baseline_tools as b,source_audit as audit
c.ROOT=HERE/'inputs'
BASE_NODES=c.raw_nodes
BASE=b.read_table(HERE/'inputs/unfolded201.native.tm')
INC=('leaf','inc',1)
c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
EXPECTED={
 5:{'dense':'30d762c8192a21936511931f35f72888d7b8249128633a5c019435fdd173ad1f',
    'native':'1d8eb733d26b98fa528864cb080335b50db8a8334dbcc141c57aacfa2d85a060',
    'sites':3715,'outcomes':4816,'symbolic_steps':1540341},
 6:{'dense':'72a35e528c1061f61e211d0bcf3a954859d2dbbcfd6b9f7846e4f970bb04e4e9',
    'native':'372d68753d206e5396312951a6be777179757598ad1384784db45764efd61fbc',
    'sites':3776,'outcomes':4877,'symbolic_steps':1565180}}
def save(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')
def sha(b):return hashlib.sha256(b).hexdigest()

def nodes(k,head):
 ns=BASE_NODES()
 assert ns['node163']==('node6','node55')
 ns['node163']=('node6','node54')
 if head:ns['node170']=(('node36',('node167','node145')),'node57')
 if k!=4:
  triple=(INC,'node60');ns['node61']=(triple,'node60' if k==5 else triple)
 return ns

def build(k,head=False,full=True,output=HERE.parent/'machines'):
 assert __debug__ and not sys.flags.optimize,'Assertions must be enabled.'
 assert k in (5,6) and not head,'This release contains only QN5 and QN6.'
 provenance=json.loads((HERE.parent/'PROVENANCE.json').read_text())
 for item in provenance['inputs']:
  assert sha((HERE.parent/item['path']).read_bytes())==item['sha256'],item['path']
 name=f'PA194Q'+('H' if head else 'N')+str(k)
 rawbase=dict(BASE);rawbase[164,1]=(1,True,114)
 if head:rawbase.update({(38,0):(0,True,11),(38,1):(1,True,122),
   (214,0):(0,True,312),(214,1):(1,True,20),(312,0):(0,True,188)})
 c.machine=lambda:(rawbase,[])
 grammar=c.read_grammar(HERE/'inputs/grammar.json')
 c.raw_nodes=lambda:nodes(4,head)
 oldsites,oldins,_=c.source(grammar)
 assert len(oldsites)==3654
 audit.BASE_NODES=c.raw_nodes
 raw,index,shape=c.build(grammar)
 assert len(raw)==402 and len(shape)==67
 raw.update({(190,0):(0,True,330),(190,1):(1,True,99 if k==5 else 330),
   (330,0):(0,True,61),(330,1):(1,True,99)})
 folds=json.loads((HERE/'inputs/folds.json').read_text())+[[41,99,[[0,False,30],[1,False,2040]]]]
 child,aliases=b.apply_folds(raw,folds)
 local=b.check_local_folds(raw,child,aliases,folds)
 assert len(raw)==404 and len(child)==388 and len(local['cases'])==32
 assert all(child[q,bit]==BASE[q,bit] for q in c.BOXSTATES for bit in (0,1))
 c.raw_nodes=lambda:nodes(k,head)
 sites,ins,contracts=c.source(grammar)
 assert len(sites)==EXPECTED[k]['sites'] and len(contracts)==EXPECTED[k]['outcomes']
 binding=audit.source_binding(grammar,oldsites,oldins,nodes(k,head),sites,ins,k)
 free=audit.emitter_audit(grammar,k)
 valid=c.validate(child,contracts)if full else None
 if full:
  assert valid['ok'],valid
  assert valid['total_steps']==EXPECTED[k]['symbolic_steps'] and valid['max_steps']==490
 seed=b.startup(child,sites[25][0])
 assert seed['steps']==58320
 dense,labels=b.dense_table(child,194)
 assert sha(b.table_text(dense).encode())==EXPECTED[k]['dense']
 assert sha(b.table_text(child).encode())==EXPECTED[k]['native']
 out=output/name;out.mkdir(parents=True,exist_ok=True)
 for fn,table in [('machine.native.tm',child),('machine.tm',dense),('raw.native.tm',raw)]:
  (out/fn).write_text(b.table_text(table))
 for fn,obj in [('labels.json',labels),('nodes.json',nodes(k,head)),('folds.json',folds),('local_cases.json',local),
  ('sites.json',[[list(p),op,arg]for p,op,arg in sites]),('instructions.json',ins),('source_binding.json',binding),('emitter_audit.json',free),
  ('source_radix4.json',dict(sites=oldsites,instructions=oldins))]:save(out/fn,obj)
 receipt={'family':name,'states':194,'transition_rows':388,'radix':k,'MP_success':'(b,w,b,0), b=d+x',
  'Shift_test':'h=1'if head else't+h=1','AX_distribution':'U(d,I(a,h))->(U(d,a)->U(d,h))',
  'source_sites':len(sites),'source_outcomes':len(contracts),'raw_states':202,'reader_states':67,'folds':8,'fold_cases':32,
  'runtime':valid,'startup':seed,'dense_sha256':sha(b.table_text(dense).encode()),
  'native_sha256':sha(b.table_text(child).encode()),'kernel_checked':False}
 save(out/'receipt.json',receipt)
 print(json.dumps(receipt),flush=True)
 return out
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--quick',action='store_true')
 ap.add_argument('--family',choices=['QN5','QN6'],action='append')
 ap.add_argument('--output',type=Path,default=HERE.parent/'machines')
 a=ap.parse_args()
 for family in a.family or ['QN5','QN6']:
  build(int(family[-1]),False,not a.quick,a.output)
