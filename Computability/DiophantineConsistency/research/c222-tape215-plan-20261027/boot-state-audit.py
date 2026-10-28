"""Read literal state maps and boot-block statements; no Lean/existing code runs."""
from pathlib import Path
import hashlib
import json
import re

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
BB = R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
DC = R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
HERE = Path(__file__).resolve().parent


def pin(p):
    return {'path': str(p), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}


def nat_list(p, name):
    text = p.read_text()
    match = re.search(r'def '+name+r'\s*:[^=]*:=\s*\[([^\]]*)\]', text, re.S)
    assert match
    body = match.group(1)
    assert re.fullmatch(r'[\s,0-9]*', body)
    return [int(s) for s in body.split(',') if s.strip()]


decimal = DC/'DecimalMachine215.lean'
dense = BB/'KDense215.lean'
to_dense = nat_list(decimal, 'toDenseList')
labels = nat_list(dense, 'denseLabels')
assert sorted(to_dense) == list(range(215)) and len(set(labels)) == 215
sparse = [labels[i] for i in to_dense]
assert sparse[0] == 0 and 230 not in sparse
inverse = {q: i+1 for i, q in enumerate(sparse)}
assert inverse[84] == 24

chunks = []
for path in sorted(BB.glob('KBoot215Chunk*.lean')):
    match = re.search(r'theorem block(\d+) : lblock \(fastOf tt215\) (\d+) ', path.read_text())
    assert match
    chunks.append({'number': int(match[1]), 'depth': int(match[2]),
                   'steps': 2**int(match[2]), 'source': pin(path)})
assert [x['number'] for x in chunks] == list(range(1,14))
assert sum(x['steps'] for x in chunks) == 95714

boot = BB/'KBoot215.lean'
text = boot.read_text()
assert 'def bootVs : List Nat := [0, 0, 0, 0, 0, 0, 4, 0, 0] ++ List.replicate 40 1' in text
assert 'def bootRight : List Bool := List.replicate 65 false ++ true :: KRuntimeCore.sepsR bootVs' in text
assert 'theorem cp_state : cp13.1 = 84 := rfl' in text
values = [0,0,0,0,0,0,4,0,0] + [1]*40
bits = [False]*65 + [True]
for v in values: bits += [False] + [True]*(v+1)
right = sum(int(b)*2**i for i,b in enumerate(bits))
pair = lambda a,b: (a+b)*(a+b+1)//2+b
result = {
    'scope': 'Read-only literal-data arithmetic, not a Lean proof or runtime execution.',
    'state_maps': {'source_pins': [pin(decimal),pin(dense)],
        'live_states': len(sparse), 'injective': len(set(sparse)) == 215,
        'sparse_live_zero_decimal_code': inverse[0],
        'sparse84_dense_index': labels.index(84),
        'sparse84_decimal_index': inverse[84]-1,
        'sparse84_decimal_positive_code': inverse[84],
        'terminal230_absent_from_live_image': 230 not in sparse,
        'max_live_sparse_label': max(sparse),
        'sparse_expansion': sparse},
    'boot': {'source':pin(boot), 'chunks':chunks, 'sum_steps':95714,
        'sparse_state':84,'decimal_state':23,'arithmetic_state_code':24,
        'left_bits':[True], 'gap':65,'physical_registers':values[:9],
        'spare_count':40,'spare_value':1,'total_blocks':len(values),
        'right_bit_length':len(bits), 'right_code':str(right),
        'candidate_numeric_boot_code':str(pair(24,pair(1,right))),
        'numeric_code_formula':'cantor 24 (cantor 1 (bitsCode KBoot215.bootRight))'},
    'limitations': ['Inverse state-map kernel theorem is proposed, not newly proved.',
        'Fixed boot blocks are already kernel-proved; this script only sums their stated clocks.',
        'No sparse-site or all-internal tape simulation follows from these data checks.'],
    'script':pin(Path(__file__).resolve())}
out=HERE/'boot-state-audit.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'output':pin(out),'boot_steps':95714,'decimal_code_for_sparse84':24,
                  'right_bits':len(bits)},indent=2))
