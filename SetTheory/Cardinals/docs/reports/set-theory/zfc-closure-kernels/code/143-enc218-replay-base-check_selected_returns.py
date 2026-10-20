#!/usr/bin/env python3
"""Independent dispatcher-to-return derivation for all13 nonzero-erase contexts."""
import collections,hashlib,json
from pathlib import Path
import symbolic_contexts as own
from review_return_contracts import translate
D=Path(__file__).resolve().parent;ROOT=D.parent
S=json.loads((ROOT/'latest219_baseline/candidate-k219/sites219.json').read_text())
R=json.loads((ROOT/'research218_encoding/RETURN_FULL_CONTRACTS.json').read_text())
M={int(k):v for k,v in json.loads((ROOT/'research218_encoding/NATIVE_TO_LEGACY.json').read_text()).items()};I={v:k for k,v in M.items()}
words=json.loads((D/'RETURN_WORDS.json').read_text());selected={r['source_index'] for r in words if r['erase_ones']>0}
assert len(selected)==13
T=own.readtm(ROOT/'latest219_baseline/candidate-k219/k219.native.tm');schemas,_=own.prove_schemata(T)
advance=own.Tape.advance;captured=[]
def hooked(self,tm,schemata):
 self.key();cur=(self.R if self.d==1 else self.L)[0]
 if self.q==103 and cur[:2]==('r',1) or self.q==113 and cur[:2]==('r',0):
  captured.append(json.dumps([self.q,self.d,self.L,self.R],separators=(',',':')))
 return advance(self,tm,schemata)
own.Tape.advance=hooked
results=[]
for i in sorted(selected):
 captured=[]
 n,_=own.case(T,schemas,S[i],False,{})
 expected=[json.dumps([I[r['state']],r['direction'],translate(r['left']),translate(r['right'])],separators=(',',':')) for r in R if r['site'][0]==i]
 assert collections.Counter(captured)==collections.Counter(expected),(i,len(captured),len(expected))
 results.append({'index':i,'site':S[i],'symbolic_rules':n,'exact_full_captures':len(captured)})
report={'status':'ALL13_SELECTED_UNBOUNDED_CASES_AND_FULL_RETURN_WORDS_PASS','cases':results,'rules':sum(r['symbolic_rules'] for r in results),'scope':'Independent native-label symbolic derivation from complete arbitrary-natural entry frames to full frame postconditions; exact captured word comparison. Includes allnonzero302eraseruns and arithmetic103/119 path. Other1419capturepremises are read/audited,not independently regenerated here.'}
(D/'SELECTED_RETURN_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
