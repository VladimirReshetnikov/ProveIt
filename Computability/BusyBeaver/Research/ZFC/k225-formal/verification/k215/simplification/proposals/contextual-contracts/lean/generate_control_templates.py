#!/usr/bin/env python3
"""Emit only finite descriptor data for KFramedControl215.

The hand-written proof outside the generated section is preserved. Lean checks
all links from the input metadata to the actual runtime and source semantics.
"""
import argparse
import hashlib
import json
from pathlib import Path

def bits(s):
    if any(c not in '01' for c in s):
        raise ValueError(s)
    return '['+', '.join('true' if c=='1' else 'false' for c in s)+']'

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('input',type=Path)
    ap.add_argument('--output',type=Path,default=Path('BusyBeaver/ZFC/KFramedControl215.lean'))
    a=ap.parse_args()
    raw=a.input.read_bytes()
    ts=json.loads(raw)['templates_data']
    if len(ts)!=35:
        raise ValueError('Expected exactly 35 templates')
    lines=['def descriptors : List Descriptor := [']
    for i,t in enumerate(ts):
        if i!=t['id']:
            raise ValueError('ID mismatch')
        key=t['key']
        kind={'CC':'cont','CB':'brk'}[key[3]]
        lines.append(f'  ⟨⟨{i}, by decide⟩, {key[1]}, {bits(key[2])}, {bits(key[6])}, .{kind} {key[4]}⟩'+(',' if i<34 else ']'))
    lines.extend(['',
      'theorem descriptor_count : descriptors.length = 35 := by decide',
      'theorem descriptor_indices : descriptors.map (fun d => d.index.val) = List.range 35 := by decide',
      'theorem all_aligned : descriptors.all aligned = true := by decide','',
      '/-- All 35 literal templates implement the recorded source action for every prefix accepted by Home. -/',
      'theorem control_contract (B : BoxLemmas tm215) (rows : KHome.Rows tm215)',
      '    (hb : KHome.Boundary tm215) {d : Descriptor} (hd : d ∈ descriptors)',
      '    (p : List Bool) {k : Nat}',
      '    (hp : KHome.scanBound 0 (p.reverse.map Seg.bit) = some k)',
      '    (n : Nat) {vs : List Nat} (hv : Valid none vs) :',
      '    Reach1 tm215 (suffixPort d.state p d.suffix n vs)',
      '      (dispatch p d.suffix d.result n vs) ∧',
      '    ∀ r : RegisterPath.Registers,',
      '      RegisterPath.execute d.action (p ++ d.suffix) r = some ⟨p ++ d.result, r⟩ :=',
      '  aligned_contract B rows hb d (List.all_eq_true.mp all_aligned d hd) p hp n hv','',
      '#print axioms all_aligned',
      '#print axioms control_contract',''])
    old=a.output.read_text()
    start='-- BEGIN GENERATED DESCRIPTORS\n'
    end='-- END GENERATED DESCRIPTORS'
    pre,body=old.split(start)
    _,post=body.split(end)
    a.output.write_text(pre+start+'\n'.join(lines)+end+post)
    print(json.dumps({'descriptors':len(ts),'input_sha256':hashlib.sha256(raw).hexdigest(),
      'output_sha256':hashlib.sha256(a.output.read_bytes()).hexdigest()},indent=2))

if __name__=='__main__':main()
