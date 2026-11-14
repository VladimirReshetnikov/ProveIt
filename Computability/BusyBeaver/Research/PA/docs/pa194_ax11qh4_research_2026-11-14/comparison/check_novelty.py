#!/usr/bin/env python3
"""Exact graph novelty against the frozen, scoped current 194-state inventory.

Compares complete tuples, not just hashes. Allows arbitrary state renaming,
every root reaching all working controls, global L/R reflection, global bit
exchange, and ignores terminal-transition write/move decoration. Bit exchange
is only a structural comparison; it does not preserve the zero-blank convention.
"""
import argparse,hashlib,json,pathlib,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent/'vendor'))
import literal_inventory as lit
import machine_classes as mc
if not __debug__:
    raise RuntimeError('Run the verifier with assertions enabled, without -O.')

def strong_form(raw):
    data=lit.parse_table(raw)
    if data is None:raise ValueError('Not a complete one-halt binary table')
    rows,states,halt=data;forms=[]
    for flip in (False,True):
      for mirror in (False,True):
        for root in sorted(states):
          labels={root:0};order=[root];out=[]
          for q in order:
            for b in (0,1):
              w,d,t=rows[q,b^flip]
              if t==halt:out.append((0,0,-1));continue
              if t not in labels:labels[t]=len(order);order.append(t)
              out.append((w^flip,(d=='R')^mirror,labels[t]))
          if len(order)==len(states):forms.append(tuple(out))
    return min(forms) if forms else None

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--candidate',action='append',type=pathlib.Path,required=True);ap.add_argument('--output',type=pathlib.Path,required=True);args=ap.parse_args()
    root=pathlib.Path(__file__).resolve().parent;inv=json.loads((root/'designs194.json').read_text())
    refs=[]
    for i,r in enumerate(inv['designs']):
      p=root/r['representative_file'];raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest()
      assert h==r['representative_sha256'],p
      cl=mc.classify(raw);assert cl['states']==194 and cl['table']==r['table_class'],p
      form=strong_form(raw);assert (form is not None)==r['spanning_root'],p
      refs.append((r,form))
      if (i+1)%20==0:print('Checked inventory graphs',i+1,flush=True)
    candidates=[];forms=[]
    for p in args.candidate:
      raw=p.read_bytes();cl=mc.classify(raw);form=strong_form(raw)
      assert cl['states']==194 and cl['reachable']==194 and form is not None,p
      matches=[r['name'] for r,f in refs if form==f]
      candidates.append({'path':str(p),'sha256':hashlib.sha256(raw).hexdigest(),'table_class':cl['table'],'states':cl['states'],'graph_reachable_from_dense_start':cl['reachable'],'strong_form_sha256':hashlib.sha256(repr(form).encode()).hexdigest(),'matches':matches,'novel_within_scope':not matches})
      forms.append(form)
    result={'snapshot':inv['summary']['snapshot'],'scope':__doc__,'historical_graphs_checked':len(refs),'spanning_graphs_checked':sum(f is not None for r,f in refs),'complete_tuple_comparison':True,'candidates':candidates,'candidate_forms_pairwise_distinct':len(set(forms))==len(forms)}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
