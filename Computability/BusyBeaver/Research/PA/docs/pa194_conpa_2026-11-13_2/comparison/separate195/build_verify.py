#!/usr/bin/env python3
"""Rebuild and verify the new separate190-based 195-state implementation.
This is an intermediate equal-state construction, not the requested <=194 result.
No network, optimizer, or proof assistant is required. Run without Python -O.
"""
from pathlib import Path
import argparse,hashlib,json,sys
import check_support as s
c=s.c
P=Path(__file__).resolve().parent
EXPECTED='f5300673492372f70b72fbbaec819593acf922981c257604fb3167ff23e55f2e'

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--export',action='store_true');args=ap.parse_args()
 s.need(__debug__ and not sys.flags.optimize,'Run without Python optimization')
 for name,digest in json.loads((P/'reference_hashes.json').read_text()).items():
  s.need(hashlib.sha256((P/name).read_bytes()).hexdigest()==digest,'input hash: '+name)
 t=c.read_grammar(P/'grammar.json');parent=c.read_grammar(P/'reference/separate196.grammar.json')
 raw,idx,shape=c.build(t);s.need(len(raw)==402 and len(idx)==67,'raw allocation')
 folds=json.loads((P/'folds.json').read_text());s.need(len(folds)==6,'fold count')
 folded,aliases=s.quotient(raw,folds);cert=s.quotient_certificate(raw,folded,folds,aliases)
 s.need(folded==s.table(P/'machine.native.tm'),'native table mismatch')
 labels=json.loads((P/'labels.json').read_text());s.need(len(labels)==196 and len(set(labels))==196 and labels[0]==74 and labels[-1]==254,'labels')
 inverse={q:i for i,q in enumerate(labels)};dense={(inverse[q],b):(w,d,inverse[n])for(q,b),(w,d,n)in folded.items()}
 s.need(dense==s.table(P/'machine.tm'),'dense table mismatch')
 s.need(hashlib.sha256(s.table_bytes(dense)).hexdigest()==EXPECTED,'literal table digest')
 reached={0};todo=[0]
 for q in todo:
  for b in (0,1):
   n=dense[q,b][2]
   if n!=195 and n not in reached:reached.add(n);todo.append(n)
 s.need(reached==set(range(195)),'graph reachability')
 sites,ins,cs=c.source(t);oldsites,oldins,oldcs=c.source(parent)
 s.need(s.word(t)==s.word(parent) and len(s.word(t))==190,'macro word changed')
 s.need([x[1:]for x in sites]==[x[1:]for x in oldsites],'primitive word changed')
 s.need(ins==oldins==s.interval_cfg(sites)==s.interval_cfg(oldsites),'ordinal source graph changed')
 s.need(len(sites)==3673 and len(cs)==4780,'source census')
 old,_=c.machine();s.need(all(folded[q,b]==old[q,b]for q in c.BOXSTATES for b in(0,1)),'protected engine changed')
 startup=s.startup(dense,labels)
 rawcheck=c.validate(raw,cs);check=c.validate(folded,cs)
 s.need(rawcheck['ok']and check['ok'],'universal symbolic branch check failed')
 source=[{'ordinal':i,'path':''.join(map(str,path)),'op':op,'arg':arg,'instruction':list(ins[i])}for i,(path,op,arg)in enumerate(sites)]
 if args.export:
  (P/'source.json').write_text(json.dumps(source,indent=2)+'\n')
  (P/'local_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
 elif (P/'source.json').exists():s.need(json.loads((P/'source.json').read_text())==source,'source export mismatch')
 receipt={'status':'PASS','target_below195_achieved':False,'working_states':195,'rows':390,'start':0,'halt':195,'AX_readers':67,'folds':6,'local_cases':cert['local_cases'],'local_durations':cert['durations'],'macro_tokens':190,'stack_interface_pushed_entries':10,'source_sites':3673,'symbolic_contracts':4780,'old_source_graph_preserved':True,'two_source_resolvers_agree':True,'complete_stack_word_preserved':True,'raw_runtime':rawcheck,'folded_runtime':check,'startup':startup,'sha256':EXPECTED,'new_kernel_checked_endpoint':False}
 if args.export:(P/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
