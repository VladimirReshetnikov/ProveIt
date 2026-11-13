#!/usr/bin/env python3
"""Generate exact dense/native PA196 transition data from pinned sources."""
from hashlib import sha256
from pathlib import Path
from zipfile import ZipFile
import argparse
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[6]
BASE=ROOT/'Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196'
LABELS_SHA='44983c537d1287d5947dec3bd8e2f9ba43657368fe8ebe75899d2ede54e7c1a3'
DENSE_SHA='e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8'
NATIVE_SHA='454254a42a9f9096b72f73ef491107713002ca32f2a51f165eee7ca299283215'

def need(ok,msg):
    if not ok: raise ValueError(msg)

def parse(data):
    rows={}
    for line in data.decode('ascii').splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        need(b in (0,1) and w in (0,1) and d in ('L','R') and (q,b) not in rows,'bad row')
        rows[q,b]=(w,d,n)
    return rows

def source_lookup(body, option_rows):
    """Interpret the pinned source's finite if-tree, rejecting unknown syntax."""
    lines=body.strip('\n').splitlines()
    read_pattern=(r'if read then some \((true|false), (true|false), (\d+)\) else some \((true|false), (true|false), (\d+)\)'
                  if option_rows else r'if read then \((true|false), (true|false), (\d+)\) else \((true|false), (true|false), (\d+)\)')
    def parse_at(i, indent):
        need(i < len(lines), 'truncated source tree')
        line=lines[i]; level=len(line)-len(line.lstrip(' '))
        need(level==indent, 'bad source indentation')
        line=line.strip()
        leaf=re.fullmatch(read_pattern,line)
        if leaf:
            def action(bits):
                w,d,n=bits
                return (int(w=='true'),'R' if d=='true' else 'L',int(n))
            values=leaf.groups()
            return ('leaf',action(values[:3]),action(values[3:])),i+1
        cond=re.fullmatch(r'if q ([<=]) (\d+) then',line)
        need(cond is not None, 'unsupported source tree line: '+line)
        left,j=parse_at(i+1,indent+2)
        need(j<len(lines), 'missing source else')
        el=lines[j];level=len(el)-len(el.lstrip(' '))
        need(level==indent, 'bad source else indentation')
        if el.strip()=='else none':
            right=('none',);j+=1
        else:
            need(el.strip()=='else', 'missing source else')
            right,j=parse_at(j+1,indent+2)
        return ('if',cond.group(1),int(cond.group(2)),left,right),j
    tree,end=parse_at(0,len(lines[0])-len(lines[0].lstrip(' ')))
    need(end==len(lines),'trailing source tree')
    def lookup(q,read):
        node=tree
        while node[0]=='if':
            _,op,n,left,right=node
            node=left if (q<n if op=='<' else q==n) else right
        return None if node[0]=='none' else node[1] if read else node[2]
    return lookup

def render():
    labels_data=(BASE/'PA196/Conjugacy.lean').read_bytes()
    dense_data=(BASE/'data/pa196.tm').read_bytes()
    literal_data=(BASE/'PA196/Literal.lean').read_bytes()
    table_data=(BASE/'PA196/Table.lean').read_bytes()
    with ZipFile(ROOT/'docs/incoming/pa_consistency_research.zip') as archive:
        native_data=archive.read('pa_consistency_research/data/pa196.native.tm')
    for data,expected,name in ((labels_data,LABELS_SHA,'labels'),(dense_data,DENSE_SHA,'dense'),(native_data,NATIVE_SHA,'native'),(literal_data,'e5ed123ad8e54d431472621d46b6f147a76ed94426efc9e9298f475e8ecca944','literal source'),(table_data,'d6e9a050dbe11969240ee0d18846b3710666b1c5b664a66d7fcedcfec19cd12f','native source')):
        need(sha256(data).hexdigest()==expected,'changed '+name+' input')
    found=re.findall(r'def labels : List Nat := \[([^\]]+)\]',labels_data.decode())
    need(len(found)==1,'missing labels')
    labels=[int(x) for x in found[0].split(',')]
    need(len(labels)==197 and len(set(labels))==197 and labels[0]==74 and labels[-1]==254,'label mapping')
    dense,native=parse(dense_data),parse(native_data)
    need(set(dense)=={(q,b)for q in range(196)for b in (0,1)} and
         set(native)=={(q,b)for q in labels[:-1]for b in (0,1)},'table census')
    for q in range(196):
        for b in (0,1):
            w,d,n=dense[q,b];need(n<=196 and native[labels[q],b]==(w,d,labels[n]),'row mismatch')
    literal_text=literal_data.decode('utf-8')
    table_text=table_data.decode('utf-8')
    literal=literal_text[literal_text.index('def transition (q : Nat)'):literal_text.index('\ndef workingLabels :')]
    literal=literal.replace('def transition (q : Nat)', 'def sourceTransition (q : Nat)',1)
    literal=literal.replace('def machine : TMN :=', 'def dense : TM :=',1)
    literal=literal.replace('some (transition q read)', 'some (sourceTransition q read)',1)
    native_source=table_text[table_text.index('def machine : TMN :='):table_text.index('\ndef workingLabels :')]
    literal_body=literal_text.split('def transition (q : Nat) (read : Bool) : Bool × Bool × Nat :=\n',1)[1].split('\n/-- A binary Turing machine',1)[0]
    native_body=native_source.split('def machine : TMN := fun q read =>\n',1)[1]
    dense_eval,native_eval=source_lookup(literal_body,False),source_lookup(native_body,True)
    need('if q < 196 then some (transition q read) else none' in literal_text,'dense guard changed')
    for q in range(196):
        for b in (0,1):
            need(dense_eval(q,b)==dense[q,b], 'dense Lean/source table mismatch')
            need(native_eval(labels[q],b)==native[labels[q],b], 'native Lean/source table mismatch')
    need(all(native_eval(254,b) is None for b in (0,1)), 'native halt not absent')
    native_source=native_source.replace('def machine : TMN :=', 'def native : TM :=',1)
    need('def dense : TM' in literal and 'sourceTransition q read' in literal and
         'def native : TM' in native_source, 'source extraction failed')
    text='''import NativeDense.Core

/-! The transition definitions below are extracted from the pinned PA196
    Literal.lean and Table.lean, with names changed but bodies unchanged. -/
namespace NativeDense
set_option maxRecDepth 100000
set_option maxHeartbeats 0

'''
    text+='def labels : Array Nat := #['+', '.join(map(str,labels))+']\n'
    text+='def label (q : Nat) : Nat := labels[q]?.getD (q+1001)\n'
    text+=literal+'\n'+native_source+'\n'
    text+='''
/- The finite check is divided into small chunks to limit kernel memory. -/
def rowCheck (q : Nat) : Bool := [false,true].all (fun b =>
  decide (native (label q) b = (dense q b).map (mapAction label)))

theorem rows_conjugate (q : Nat) (hq : q < 197) (b : Bool) :
    native (label q) b = (dense q b).map (mapAction label) := by
  have h := List.all_eq_true.mp exact_rows q (List.mem_range.mpr hq)
  change rowCheck q = true at h
  unfold rowCheck at h
  have hb : b ∈ [false,true] := by cases b <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp h b hb)

theorem next_bounds : (List.range 197).all (fun q => [false,true].all (fun b =>
  match dense q b with | none => true | some (_,_,t) => decide (t < 197))) = true := by
  decide

theorem next_bounded (q : Nat) (hq : q < 197) (b w d : Bool) (t : Nat)
    (h : dense q b = some (w,d,t)) : t < 197 := by
  have hh := List.all_eq_true.mp next_bounds q (List.mem_range.mpr hq)
  have hb : b ∈ [false,true] := by cases b <;> simp
  have ht := List.all_eq_true.mp hh b hb
  rw [h] at ht
  exact of_decide_eq_true ht

theorem labels_count : labels.size = 197 := by decide
theorem labels_nodup : labels.toList.Nodup := by decide
theorem starts : label 0 = 74 := by decide
theorem halts : label 196 = 254 := by decide

theorem dense_native_halts_iff :
    Halts native (zc 74 [] []) ↔ Halts dense (zc 0 [] []) := by
  have h := halts_conjugate rows_conjugate next_bounded (zc 0 [] []) (by decide)
  simpa [mapConf,zc,starts] using h

theorem dense_native_reach_and_stop_iff :
    ReachAndStop native (zc 74 [] []) ↔ ReachAndStop dense (zc 0 [] []) := by
  rw [← halts_iff_reach_and_stop, ← halts_iff_reach_and_stop]
  exact dense_native_halts_iff

theorem dense_native_nonhalting_iff :
    (¬ Halts native (zc 74 [] [])) ↔ (¬ Halts dense (zc 0 [] [])) := by
  constructor <;> intro h hh
  · exact h (dense_native_halts_iff.mpr hh)
  · exact h (dense_native_halts_iff.mp hh)

#print axioms exact_rows
#print axioms dense_native_halts_iff
#print axioms dense_native_reach_and_stop_iff
#print axioms dense_native_nonhalting_iff
end NativeDense
'''
    # Prove the finite table comparison in independent batches, then join them.
    marker = 'theorem rows_conjugate'
    chunks = [(i,min(16,197-i)) for i in range(0,197,16)]
    pieces = ''.join(f"theorem rows_chunk_{i} : (List.range' {offset} {length}).all rowCheck = true := by decide\n"
                     for i,(offset,length) in enumerate(chunks))
    ranges = ' ++ '.join(f"(List.range' {offset} {length})" for offset,length in chunks)
    witnesses = ', '.join(f'rows_chunk_{i}' for i in range(len(chunks)))
    pieces += (f"\ntheorem exact_rows : (List.range 197).all rowCheck = true := by\n"
               f"  have h : List.range 197 = {ranges} := by decide\n"
               f"  rw [h]\n  simp only [List.all_append, {witnesses}, Bool.and_self]\n\n")
    text=text.replace(marker,pieces+marker,1)
    return text

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    target=HERE/'NativeDense/Tables.lean'; text=render()
    if args.check:
        need(target.read_text()==text,'generated Lean table differs')
        print('Pinned upstream Lean sources, dense table, native table, and generated source: OK')
    else:
        target.write_text(text)
        print('Wrote',target)
if __name__=='__main__':main()
