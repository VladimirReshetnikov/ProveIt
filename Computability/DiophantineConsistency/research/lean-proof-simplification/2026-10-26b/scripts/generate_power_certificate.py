#!/usr/bin/env python3
"""Extract compact power labels from the pinned Lean statement data.

Python verifies local multiplication labels as a diagnostic.  The generated
Lean files independently check the finite certificate with `decide +kernel`.
Python success is not a Lean proof.  No repository files are modified.
"""
from pathlib import Path
import json, re
import argparse

parser=argparse.ArgumentParser()
parser.add_argument('source',type=Path,help='DiophantineConsistency module directory')
parser.add_argument('output',type=Path)
args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=True)
metrics={}
for prefix, suffix, fixed, count, base in [('Gap','66',11,484,20),('Split','59',12,515,36)]:
    parent=f'{prefix}Circuit{suffix}'
    original=(args.source/f'{prefix}CircuitSteps{suffix}.lean').read_text()
    powers={int(i):int(n) for i,n in re.findall(
        r'theorem natural_power_(\d+).*?naturalRegister p x \d+ = naturalRegister p x \d+ \^ (\d+)',original,re.S)}
    assert len(powers)==(86 if prefix=='Gap' else 107)
    labels=[0]*count;labels[base]=1
    for i,n in powers.items():labels[i]=n
    source=(args.source/f'{parent}.lean').read_text().split('def naturalNodes :',1)[1].split('def naturalOutput',1)[0]
    nodes=re.findall(r'\.(literal|input|constant|add|sub|mul)\s+([^\n]+)',source)
    assert len(nodes)==count,(len(nodes),count)
    for i,n in powers.items():
        kind, operands=nodes[i]
        assert kind=='mul',(i,kind)
        a,b=map(int,re.findall(r'\d+',operands)[:2])
        assert a<i and b<i
        assert labels[a]>0 and labels[b]>0 and labels[a]+labels[b]==n,(i,n,a,b)
    table='\n'.join('  '+','.join(map(str,labels[k:k+24]))+(',' if k+24<count else '') for k in range(0,count,24))
    ns=f'{prefix}PowerCertificate'
    out=f'''import DiophantineConsistency.ArithmeticDAGPowers
import DiophantineConsistency.{parent}

/-! Proposed compact replacement for the generated pure-power proof chains.
The circuit and power exponents are unchanged.  Source SHA is recorded in the
accompanying review.  Compile this file before considering it validated. -/
namespace DiophantineConsistency.ProofSimplification.{ns}
open ArithmeticDAG
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000

def labelsData : List ℕ := [
{table}]

def label (i : ℕ) : ℕ := labelsData.getD i 0

private theorem label_steps : ∀ i : Fin {count}, i.val ≠ {base} → label i.val ≠ 0 →
    PowerStep {parent}.naturalNodes label i.val := by
  decide +kernel

theorem power {{R : Type*}} [CommRing R] (p : Fin {fixed} → R) (x : Fin 9 → R)
    (i : ℕ) (hi : i < {count}) (hp : label i ≠ 0) :
    value {parent}.naturalNodes i p x =
      value {parent}.naturalNodes {base} p x ^ label i := by
  apply run_power p x {parent}.naturalNodes {parent}.natural_topological label {base}
    (by decide +kernel) (fun j hj => label_steps ⟨j, by
      simpa only [{parent}.natural_length] using hj⟩) i
  · simpa only [{parent}.natural_length] using hi
  · exact hp

-- An unchanged high-exponent fact, obtained without a chain of ring proofs.
example {{R : Type*}} [CommRing R] (p : Fin {fixed} → R) (x : Fin 9 → R) :
    value {parent}.naturalNodes {max(powers)} p x =
      value {parent}.naturalNodes {base} p x ^ {powers[max(powers)]} :=
  power p x {max(powers)} (by decide) (by decide)

#print axioms power
end DiophantineConsistency.ProofSimplification.{ns}
'''
    path=args.output/(ns+'.lean');path.write_text(out)
    metrics[parent]={'powers_checked_by_python':len(powers),'label_count':count,
      'base_index':base,'new_lean_file_lines':len(out.splitlines()),
      'largest_test_index':max(powers),'test_exponent':powers[max(powers)],
      'validation':'Python label check passed; Lean compiler validation pending'}
(args.output/'power_certificate_metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
print(json.dumps(metrics,indent=2))
