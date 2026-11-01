#!/usr/bin/env python3
"""Audit the 86-page fixed block, actual Lean caches and whole fixed coefficients.

This is a fixed-recipe reconstruction, not a general TeX/Lean parser. It imports
no repository program. All input files are read as inert text.
"""
import ast
import hashlib
import json
import re
from pathlib import Path

BASE = Path(__file__).resolve().parents[2]
LEAN = BASE / 'Lean/DiophantineConsistency'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(value):
    return hashlib.sha256(value).hexdigest()


def digest(value):
    return sha(json.dumps(value, separators=(',', ':'), sort_keys=True).encode())


def decode(number):
    mask = number % 2**636
    payload = number // 2**636
    discoveries = [(mask >> j) & 1 for j in range(430)]
    sigma, prefix, radices = [0], [1], []
    for bit in discoveries:
        radix = (sigma[-1] + 2)**(1 - bit)
        radices.append(radix)
        prefix.append(prefix[-1] * radix)
        sigma.append(sigma[-1] + bit)
    digits = [(payload // prefix[j]) % radices[j] for j in range(430)]
    remaining, successive = payload, []
    for radix in radices:
        remaining, digit = divmod(remaining, radix)
        successive.append(digit)
    require(successive == digits, 'prefix versus successive division')
    require(remaining == payload // prefix[-1], 'complete prefix endpoint')
    marks = [(mask >> (430 + q)) & 1 for q in range(215)]
    tally, flags = 0, []
    for mark in marks:
        flags.append(14 + mark * (((remaining >> (4 * tally)) & 15) - 14))
        tally += mark
    raw = [sigma[j + 1] - digits[j] for j in range(430)]
    actions = [[(flags[j//2] >> (2*(j%2))) & 1,
                (flags[j//2] >> (2*(j%2)+1)) & 1,
                raw[j] % 216] for j in range(430)]
    return actions, raw, sigma, prefix, tally


tex = (BASE / 'equation86.tex').read_text()
old = (BASE / 'equation.tex').read_text()
historic = (BASE / 'candidates/one-page-padding-staircase-carrier65-2011/equation.tex').read_text()
def constant_block(value):
    start = value.index(r'\textbf{The four fixed integers.}')
    stop = value.index(r'\endgroup', value.index(r'\textbf{The integer $\mathcal A$', start)) + len(r'\endgroup')
    return value[start:stop]
block = constant_block(tex)
require(block == constant_block(old) == constant_block(historic), 'all three actual constant blocks agree')
require(sha(block.encode()) == 'e5e7b58b54e57badc97ba6ee7f7577ec8e858c88189474723ce28ae629b0a6c6', 'peer-reviewed constant block hash')
data = (LEAN / 'WangTiles942Data.lean').read_text()
decimal = (LEAN / 'DecimalMachine215.lean').read_text()
printed = ''.join(re.findall(r'^([0-9]+)\\par$', tex, re.M))
require(len(printed) == 715, 'complete 715-digit page numeral')
seed = int(printed)
lean_seed = int(re.search(r'def seed : ℕ := ([0-9]+)', decimal).group(1))
require(seed == lean_seed, 'actual printed numeral equals Lean numeral')
actions, raw, sigma, prefix, flag_count = decode(seed)
cache_text = data.split('def actionCache', 1)[1].split('def actionNat', 1)[0]
cached = [[int(w == 'true'), int(d == 'true'), int(q)]
          for w, d, q in re.findall(
              r'\((true|false),\s*(true|false),\s*([0-9]+)\)', cache_text)]
require(len(cached) == 430 and cached == actions, 'every cached action')
require(actions[0] == [1, 1, 1], 'actual first target is discovery state one')
require([j for j, r in enumerate(raw) if r < 0] == [125], 'unique signed halt')
require(raw[125] == -1 and actions[125][2] == 215, 'signed halt target')
require(sigma[-1] == 214 and len(prefix) == 431, 'all prefix endpoints')

targets = [sorted({a[2] for a in actions if a[1] == d}) for d in (0, 1)]
target_text = data.split('def targetList', 1)[1].split('def targets (', 1)[0]
target_arrays = re.findall(r'\[([0-9,\s]+)\]', target_text)
require(len(target_arrays) == 2, 'two literal target arrays')
target_cache = [ast.literal_eval('[' + s + ']') for s in target_arrays]
require(target_cache == [targets[1], targets[0]], 'entire target lists')
require([len(t) for t in targets] == [45, 199], 'distinct target counts')


def rail(d, q):
    return 205 - 199*d + sum(t < q for t in targets[d])


rails = [[rail(d, q) for q in range(216)] for d in (0, 1)]
rail_text = data.split('def railCache', 1)[1].split('theorem targetList_nodup', 1)[0]
rail_arrays = re.findall(r'#\[([0-9,\s]+)\]', rail_text)
require(len(rail_arrays) == 2, 'two literal rail arrays')
rail_cache = [ast.literal_eval('[' + s + ']') for s in rail_arrays]
require(rail_cache == [rails[1], rails[0]], 'all 432 rail-cache values')
require([rail(0, 0), rail(1, 0), rail(1, 1)] == [205, 6, 7], 'zero/one rails')
require([rail(0, 216), rail(1, 216)] == [250, 205], 'post-cache rails')

rows = [(0, (2, 435, 3, 1))]
transitions, copies, signals, tail = [], [], [[], []], []
for j, (write, direction, target) in enumerate(actions):
    q, b = divmod(j, 2)
    transitions.append((j+1, ((1-direction)*rail(0, target), 2*q+b+2,
                              direction*rail(1, target), write)))
for a in (0, 1):
    for b in (0, 1):
        copies.append((433-2*a+b, (0, 432*a+b, 0, 432*a+b)))
for d in (0, 1):
    for q in targets[d]:
        for b in (0, 1):
            r = rail(d, q)
            signals[d].append((423+2*r+b, (d*r, b, (1-d)*r, 2*q+b+2)))
for a in (0, 1):
    for b in (0, 1):
        tail.append((923+2*a+b, (0, 432*a+b, 0, 438)))
tail += [(927, (2, 434, 2, 0)), (928, (3, 436, 4, 4)), (929, (4, 436, 4, 0))]
tail += [(496+t, (1, 438, 1, t)) for t in (434, 435, 436)]
tail += [(933+3*a+b, (a*a, 437, b, 437)) for a in range(3) for b in range(3)]
rows += transitions + copies + signals[0] + signals[1] + tail
require(len(rows) == 942, 'complete table row count')
require(sorted(i for i, _ in rows) == list(range(942)), 'exact index partition')
tiles = [tile for _, tile in sorted(rows)]
require(len(set(tiles)) == 942, 'all tiles distinct, independent numerical check')
require(all(0 <= w < 256 and 0 <= e < 256 and 0 <= n <= 438 and 0 <= s <= 438
            for w, n, e, s in tiles), 'all four color bounds')
require(tiles[1] == (0, 2, 7, 1), 'first transition tile')
require(tiles[928] == (3, 436, 4, 4), 'initializer tile')
require(tiles[928][3] == 2*actions[0][2]+2, 'actual first-target initializer')


def weight(tile):
    w, n, e, s = tile
    return 1 + 2**10 * (1 + w + 2**8*n + 2**17*e + 2**25*s)


weights = [weight(t) for t in tiles]
require(all(0 <= c < 2**44 for c in weights), 'untruncated weight bounds')
require(len(set(weights)) == 942, 'distinct packed weights')
positions = [0]
pair_count = 0
for i in range(1, 942):
    total = 0
    for j in range(1, 942):
        numerator = 2**44 - 1 + weights[j] - weights[i]
        require(numerator >= 0, 'natural rank subtraction is exact')
        result = numerator // 2**44
        require(result == int(weights[j] > weights[i]), 'strict floor comparison')
        pair_count += 1
        total += result
    positions.append(1+total)
require(pair_count == 885481, 'all non-Start pair comparisons')
require(sorted(positions) == list(range(942)), 'numerical physical permutation')
require(positions[928] == 504, 'initializer physical rank')
require(weights[0] == 34876427265, 'printed Start packed weight')

score = lambda tile: int(weight(tile) > weights[928])
group_scores = [sum(score(t) for _, t in family)
                for family in (transitions, copies, signals[1], signals[0], tail)]
require(group_scores == [0, 2, 395, 90, 16], 'independent initializer rank groups')

controls = {}
controls['nat_subtraction_at_halt'] = max(raw[125], 0) % 216 != actions[125][2]
controls['omitted_outer_mod_at_halt'] = raw[125] != actions[125][2]
controls['wrong_nonempty_zero_interval'] = 6+int(0 in targets[1]) != rail(1, 0)
controls['omitted_halt_signal_rows'] = len(rows)-2 != 942
controls['dense93_used_without_conjugacy'] = 2*93+2 != tiles[928][3]
controls['west_east_swap_changes_weight'] = weight((3, 435, 2, 1)) != weights[0]
controls['first_decimal_digit_mutation'] = decode(seed+10**714)[0] != actions
controls['last_decimal_digit_mutation'] = decode(seed+1)[0] != actions
require(all(controls.values()), 'all concrete negative controls distinguish the binding')

# Reconstruct the exact printed port recipes from the verified finite decoder.
# These hand-transcribed formulae are checked against the pinned TeX block above;
# this program is not a general-purpose Lean or TeX parser.
import gzip
radix = 2**47
geo = lambda r, n: sum(r**j for j in range(n))
beta = radix**2011 - 1
low = beta - geo(radix,951) - radix**960 * geo(radix,26) - radix**1004
high = 8*geo(radix,917) - 4 + (2**45-4)*radix**1005 + radix**960*geo(radix,9) + radix**987*geo(radix,8) + radix**1004
# Clear all denominators in the printed Laurent expression without truncation.
entries = list(zip(weights, positions))
entries += [(2**(10+j),978+j) for j in range(8)]
entries += [(2**(18+j),960+j) for j in range(9)]
entries += [(2**(27+j),969+j) for j in range(8)]
entries += [(2**(35+j),942+j) for j in range(9)]
require(len(entries) == 976 and all(0 <= p <= 1005 for _,p in entries), 'all Phi terms and nonnegative reflected exponents')
kernel = radix**18 + radix**1004 + radix**2020 + sum(2*w*radix**(1005-p) for w,p in entries)
ports = {'beta':beta,'K':kernel,'MC':low,'MF_source':beta+high}
coefficient_dir = BASE / 'candidates/one-page-padding-staircase-carrier65-2011/coefficients'
port_records = {}
for name,value in ports.items():
    raw = value.to_bytes((value.bit_length()+7)//8, 'big')
    require(raw == gzip.decompress((coefficient_dir / (name+'.bin.gz')).read_bytes()), 'complete fixed port equals preserved coefficient '+name)
    port_records[name] = {'bytes':len(raw),'sha256':sha(raw)}
require(port_records['K']['sha256'] == '64a62b9e1eb8642492a159fc5c3a2e1c131a99c0e2f1e3b8b90fac9241166ec7', 'independently reviewed complete K digest')
require(0 < low < beta < beta+high < 2*beta, 'fixed port inequalities')

files = ['equation86.tex', 'equation.tex', 'Lean/DiophantineConsistency/DecimalMachine215.lean']
files += ['Lean/DiophantineConsistency/'+name+'.lean' for name in
          ('WangTiles942Data', 'WangTiles942TableData', 'WangTiles942Core', 'WangTiles942', 'WangTiles942Checks', 'CurrentMaskData2011', 'CurrentMasks2011', 'CurrentMaskRecipes2011', 'CurrentKernelData2011', 'CurrentKernel2011', 'CurrentWindowCarry2011', 'AdaptiveDirectOrdinate86Literal')]
report = {
    'fixed_port_records':port_records, 'constant_block_sha256':sha(block.encode()),
    'result': 'PASS', 'source_sha256': {f: sha((BASE/f).read_bytes()) for f in files},
    'decimal_digits': len(printed), 'decimal_ascii_sha256': sha(printed.encode()),
    'actions': len(actions), 'prefix_endpoints': len(prefix), 'discoveries': sigma[-1],
    'flag_nibbles': flag_count, 'halt_action': 125, 'raw_halt_target': raw[125],
    'target_counts': [len(t) for t in targets], 'rail_values_checked': 432,
    'tile_rows': len(rows), 'color_sums': [sum(t[k] for t in tiles) for k in range(4)],
    'weight_sum': sum(weights), 'doubled_weight_sum': 2*sum(weights),
    'rank_comparisons': pair_count, 'initializer_position': positions[928],
    'initializer_rank_group_sums': group_scores,
    'canonical_json_sha256': {name: digest(obj) for name, obj in
                              [('actions', actions), ('targets', targets), ('rails', rails),
                               ('tiles', tiles), ('weights', weights), ('positions', positions)]},
    'negative_controls': controls,
}
print(json.dumps(report, indent=2, sort_keys=True))
