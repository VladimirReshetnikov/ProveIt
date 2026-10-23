#!/usr/bin/env python3
"""Generate exact caller checks in bounded-memory kernel-checking modules.

The emitter is untrusted. Each shard is checked against the same maintained
source program, roles and table; the final aggregate is proved compositionally.
"""
import argparse, hashlib, json, subprocess, sys, tempfile
from pathlib import Path

def bits(s):
    if any(c not in '01' for c in s):
        raise ValueError(s)
    return 'bits "' + s + '"'

OPEN = 'open KZip KRuntimeCore KLeftFrame KFramedTemplates KFrameContracts KTableCore\n'
NS = 'namespace SetTheory.BusyBeaver.ZFC.KFrameCallers\n'
END = 'end SetTheory.BusyBeaver.ZFC.KFrameCallers\n'
OPTIONS = 'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--input', type=Path, required=True)
    ap.add_argument('--directory', type=Path, required=True)
    ap.add_argument('--batch-size', type=int, default=64)
    args = ap.parse_args()
    data = json.loads(args.input.read_text())
    out = args.directory
    out.mkdir(parents=True, exist_ok=True)
    core = 'import FrameContracts\n\n'+NS+OPEN+OPTIONS+'''
def bits (s : String) : List Bool := s.toList.map (fun c => c == '1')

def metas : List Meta := [
'''
    for t in data['templates_data']:
        _, q, s, op, k, _, e, *rest = t['key']
        core += f'  ⟨{q}, {bits(s)}, {bits(e)}, {str(op=="CB").lower()}, {k}⟩,\n'
    core += ''']

def metaAt (i : Nat) : Meta := metas[i]?.getD default
def templateAt (i : Nat) : LocalTemplate := templates[i]?.getD default

def shapeCheck : Bool :=
  decide (metas.length = templates.length) &&
    (List.range metas.length).all (fun i => decide (Shape (metaAt i) (templateAt i)))

theorem shapes_checked : shapeCheck = true := by decide +kernel

def checkCaller (c : Caller) : Bool :=
  decide (c.templateIndex < metas.length) &&
    decide (CallerOK (metaAt c.templateIndex) (templateAt c.templateIndex) c)

#print axioms shapes_checked
'''+END
    (out/'FrameCallerCore.lean').write_text(core)
    records = data['guard_records']
    batches = []
    for start in range(0, len(records), args.batch_size):
        number = start // args.batch_size
        name = f'callerBatch{number:03d}'
        module = f'FrameCallerBatch{number:03d}'
        source = 'import FrameCallerCore\n\n'+NS+OPEN+OPTIONS
        source += f'def {name} : List Caller := [\n'
        for c in records[start:start+args.batch_size]:
            source += f'  ⟨{bits(c["pc"])}, {bits(c["prefix"])}, {c["template"]}⟩,\n'
        source += ']\n\n'
        source += f'theorem {name}_checked : {name}.all checkCaller = true := by decide +kernel\n'
        source += f'\n#print axioms {name}_checked\n'+END
        (out/(module+'.lean')).write_text(source)
        batches.append((module, name))
    # Reuse the generic post-check theorems from the maintained monolithic emitter.
    # It is read as text only. Both emitters preserve the same public statements.
    with tempfile.TemporaryDirectory(prefix='k215-caller-emission-') as temporary:
        whole = Path(temporary)/'FrameCallers.lean'
        subprocess.run([sys.executable, str(Path(__file__).with_name('generate_callers.py')),
            '--input', str(args.input), '--output', str(whole)], check=True,
            capture_output=True, text=True)
        original = whole.read_text()
    tail = original[original.index('theorem caller_ok'):]
    head = ''.join('import '+module+'\n' for module, _ in batches)+'\n'+NS+OPEN+OPTIONS
    head += 'def callers : List Caller :=\n  '+' ++\n  '.join(name for _, name in batches)+'\n\n'
    head += f'theorem caller_count : callers.length = {len(records)} := by decide +kernel\n'
    head += 'theorem callers_checked : callers.all checkCaller = true := by\n'
    head += '  simp only [callers, List.all_append,\n    '+',\n    '.join(name+'_checked' for _,name in batches)+', Bool.true_and]\n\n'
    (out/'FrameCallers.lean').write_text(head+tail)
    result = dict(templates=len(data['templates_data']), callers=len(records),
        batch_size=args.batch_size, batches=len(batches),
        input_sha256=hashlib.sha256(args.input.read_bytes()).hexdigest(),
        modules=['FrameCallerCore']+[module for module,_ in batches]+['FrameCallers'])
    (out/'CALLER_SHARDS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

if __name__ == '__main__':
    main()
