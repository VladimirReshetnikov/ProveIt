#!/usr/bin/env python3
"""Read pinned Lean data; never execute repository code."""
from pathlib import Path
import re,json,hashlib,difflib
ROOT=Path(__file__).resolve().parent
SRC=ROOT/'sources'
PIN='cbf94cb552a3b49509e0eee80e7455d4eb5974c6'
FILES=['Dag222.lean','Dag219.lean','DagDom.lean','DagPerm.lean','L2AxiomsPerm.lean','L2AxiomsDom.lean']
def require(c,m):
 if not c:raise ValueError(m)
def rows(s):
 result={}
 for line in s.splitlines():
  match=re.match(r'\s*\|\s*(\d+)\s*=>\s*(.*)$',line)
  if match is None:continue
  n=int(match.group(1));body=match.group(2)
  edges=re.findall(r'\.(node|inc|decnz|cont|brk|halt)\b\s*(\d*)',body)
  require(len(edges)==2,'unparsed numbered row: '+line)
  require(n not in result,'duplicate node')
  result[n]=tuple((tag,int(value) if value else None) for tag,value in edges)
 return result

def infer(nodes,decode,fuel,n,stop=457):
 out=[];trace=[]
 while n!=stop:
  if fuel==0 or n not in nodes:return None,trace
  left,right=nodes[n]
  if left[0]!='node' or right[0]!='node':return None,trace
  m,nxt=left[1],right[1]
  if m not in decode:return None,trace
  out.append(decode[m]);trace.append([n,m,nxt]);n=nxt;fuel-=1
 return out,trace
def checked(nodes,atom_nodes,n,word):
 for atom in word:
  if n not in nodes:return False
  left,right=nodes[n]
  if left[0]!='node' or right[0]!='node':return False
  m,nxt=left[1],right[1]
  if m!=atom_nodes[atom]:return False
  n=nxt
 return n==457
helper='''import BusyBeaver.ZFC.RMDag

/-! Proposed data extractor. Soundness remains in the existing axWordCheck theorem.
This draft has not been compiled. It adds no axiom or soundness theorem. -/
namespace SetTheory.BusyBeaver.ZFC.MacroWordInference
open RMDag

def inferWord {α : Type} (nodes : Nat → Edge × Edge)
    (decode : Nat → Option α) (stop : Nat) : Nat → Nat → Option (List α)
  | 0, n => if n = stop then some [] else none
  | fuel + 1, n =>
    if n = stop then some [] else
      match nodes n with
      | (.node m, .node next) => do
        let a ← decode m
        let rest ← inferWord nodes decode stop fuel next
        pure (a :: rest)
      | _ => none

end SetTheory.BusyBeaver.ZFC.MacroWordInference
'''
def main():
 texts={f:(SRC/f).read_text() for f in FILES}
 base=rows(texts['Dag222.lean']);base.update(rows(texts['Dag219.lean']));dom=base|rows(texts['DagDom.lean']);perm=dom|rows(texts['DagPerm.lean'])
 out=ROOT/'drafts';out.mkdir(exist_ok=True);(out/'MacroWordInference.lean').write_text(helper)
 receipt={'status':'PASS','pin':PIN,'source_sha256':{f:hashlib.sha256((SRC/f).read_bytes()).hexdigest() for f in FILES},'lanes':{},'drafts_compiled':False}
 total_before=total_after=0
 for lane,nodes in [('Perm',perm),('Dom',dom)]:
  name='L2Axioms'+lane+'.lean';s=texts[name]
  block=s.split('def AXAtom.node',1)[1].split('def AXAtom.effect',1)[0]
  atoms=dict((a,int(n)) for a,n in re.findall(r'\.([a-z0-9]+)\s*=>\s*(\d+)',block))
  require(len(atoms)==13 and len(set(atoms.values()))==13,'macro decoder map')
  decode={n:a for a,n in atoms.items()}
  match=re.search(r'def axWord : List AXAtom := \[(.*?)\]',s,re.S);require(match is not None,'word literal')
  word=re.findall(r'\.([a-z0-9]+)',match.group(1));generated,trace=infer(nodes,decode,156,236)
  require(len(word)==156 and generated==word,'literal word mismatch');require(checked(nodes,atoms,236,generated),'old checker')
  failed,_=infer(nodes,decode,155,236);require(failed is None and not checked(nodes,atoms,236,failed or []),'fuel negative control')
  wrong=decode.copy();wrong[166]='par2';bad,_=infer(nodes,wrong,156,236);require(bad is not None and not checked(nodes,atoms,236,bad),'wrong decoder control')
  corrupt=nodes.copy();corrupt[236]=(('node',166),('node',457));bad,_=infer(corrupt,decode,156,236);require(bad is not None and not checked(nodes,atoms,236,bad),'wrong extractor source control')
  corrupt[236]=(('decnz',166),('node',457));bad,_=infer(corrupt,decode,156,236);require(bad is None,'non-node shadow control')
  replacement=f'def axWord : List AXAtom :=\n  (MacroWordInference.inferWord dag{lane}.nodes AXAtom.decode 457 156 236).getD []'
  overlay=s[:match.start()]+replacement+s[match.end():]
  decode_def='def AXAtom.decode (n : Nat) : Option AXAtom :=\n  (['+', '.join('.'+a for a in atoms)+'] : List AXAtom).find?\n    (fun a => a.node == n)\n\n'
  overlay=overlay.replace('theorem AXAtom.run',decode_def+'theorem AXAtom.run',1)
  overlay='import BusyBeaver.ZFC.MacroWordInference\n'+overlay
  (out/name).write_text(overlay)
  patch=''.join(difflib.unified_diff(s.splitlines(True),overlay.splitlines(True),fromfile='a/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'+name,tofile='b/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'+name))
  (out/(name+'.patch')).write_text(patch)
  before=len(s.encode());after=len(overlay.encode());total_before+=before;total_after+=after
  receipt['lanes'][lane]={'word_length':156,'atom_kinds':13,'stop':457,'start':236,'trace':trace,'literal_word_matches':True,'old_checker_accepts':True,'negative_controls_rejected':4,'source_bytes':before,'overlay_bytes':after,'axWord_checked_and_ax_eval_proofs_unchanged':True}
 receipt['size']={'old_two_modules_bytes':total_before,'new_two_modules_bytes':total_after,'new_helper_bytes':len(helper.encode()),'net_source_bytes_saved':total_before-total_after-len(helper.encode()),'old_two_module_lines':310,'new_two_modules_plus_helper_lines':316,'k215_lane_only_bytes_saved':receipt['lanes']['Perm']['source_bytes']-receipt['lanes']['Perm']['overlay_bytes']-len(helper.encode()),'scope':'Exact draft-text size, not a compiled or performance claim.'}
 (ROOT/'AX_INFERENCE_AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({'status':'PASS','size':receipt['size'],'lanes':{k:{x:v[x] for x in ['word_length','negative_controls_rejected']} for k,v in receipt['lanes'].items()}},indent=2))
if __name__=='__main__':main()
