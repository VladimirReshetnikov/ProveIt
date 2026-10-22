"""Independent finite audit of the new Wang943 compiler.

This program imports neither the proposed builder nor any upstream program.
It reads only the inert transition table and JSON products, independently
reconstructs the language and compiler constants, and checks their contracts.
"""
from pathlib import Path
from collections import Counter, defaultdict
from hashlib import sha256
import json

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'compiler'
TABLE = BASE / 'upstream/k215.tm'
HASH = 'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090'
assert sha256(TABLE.read_bytes()).hexdigest() == HASH
transitions = {}
for raw in TABLE.read_text().splitlines():
    if not raw or raw.startswith('#'):
        continue
    q, read, write, direction, target = raw.split()
    q, read, write, target = map(int, (q, read, write, target))
    assert direction in ('L','R') and 0 <= q < 215
    assert read in (0,1) and write in (0,1) and 0 <= target <= 215
    assert (q,read) not in transitions
    transitions[q,read] = (write,direction,target)
assert set(transitions) == {(q,v) for q in range(215) for v in (0,1)}
assert transitions[0,0] == (1,'R',93)
assert transitions[68,1] == (1,'R',215)

def head(q, symbol):
    return 2 + 2*q + symbol

right_targets = sorted({q for _,d,q in transitions.values() if d == 'R'})
left_targets = sorted({q for _,d,q in transitions.values() if d == 'L'})
right_signal = {q: 6 + right_targets.index(q) for q in right_targets}
left_signal = {q: 6 + len(right_targets) + left_targets.index(q) for q in left_targets}
group = defaultdict(set)
for (q,bit),(write,direction,target) in transitions.items():
    if direction == 'R':
        group['working'].add((0,head(q,bit),right_signal[target],write))
    else:
        group['working'].add((left_signal[target],head(q,bit),0,write))
for bit in (0,1):
    group['halt'].add((0,head(215,bit),0,head(215,bit)))
    group['headless'].add((0,bit,0,bit))
    for q in right_targets:
        group['arrive_right'].add((right_signal[q],bit,0,head(q,bit)))
    for q in left_targets:
        group['arrive_left'].add((0,bit,left_signal[q],head(q,bit)))
for north in (0,1,432,433):
    group['finish'].add((0,north,0,438))
group['phase'].update(((2,434,2,0),(2,435,3,1),(3,436,4,188),(4,436,4,0)))
group['horizontal'].update((1,438,1,south) for south in (434,435,436))
group['vertical'].update((west,437,east,437) for west in (0,1,4) for east in (0,1,2))
group['forbidden'].add((5,0,0,0))
expected_set = set().union(*group.values())
assert len(expected_set) == sum(map(len,group.values())) == 943
start, forbidden = (2,435,3,1), (5,0,0,0)
expected_tiles = [start,forbidden] + sorted(expected_set - {start,forbidden})
actual_tiles = [tuple(tile) for tile in json.loads((BASE/'wang943_tiles.json').read_text())]
assert actual_tiles == expected_tiles
# Every signal has exactly the intended producer and consumer classes.
for target,signal in right_signal.items():
    assert {t for t in expected_set if t[2]==signal} <= group['working']
    assert {t for t in expected_set if t[0]==signal} == {
        (signal,bit,0,head(target,bit)) for bit in (0,1)}
for target,signal in left_signal.items():
    assert {t for t in expected_set if t[0]==signal} <= group['working']
    assert {t for t in expected_set if t[2]==signal} == {
        (0,bit,signal,head(target,bit)) for bit in (0,1)}
assert not any(t[2] == 5 for t in expected_set)  # forbidden has no west neighbor
assert all((t[1]==437) == (t[3]==437) for t in expected_set)
assert {t for t in expected_set if t[1]==438} == group['horizontal']
assert {t for t in expected_set if t[3]==438} == group['finish']
assert {t for t in expected_set if t[1] in (434,435,436)} == group['phase']
assert {t for t in expected_set if t[3] in (434,435,436)} == group['horizontal']
assert all(max(t) < 512 for t in expected_set)

# Reconstruct constants without reading the proposed scalar recipe at runtime.
k, bits, A = 943, 10, 1024
copy = [[1023+j for j in range(10)], [1013+j for j in range(10)],
        [1003+j for j in range(10)], [983+j for j in range(10)]]
M, H, T1, T2 = 1095, 17551, 37272, 56986
anchors = [1095,2190,4380,9855]
dummies = [1063,1064]
E = set(range(k)) | set(sum(copy, [])) | set(anchors) | set(dummies)
assert len(E)==989 and max(E)==9855
assert len(E)==k+4*bits+4+2
c = {}
for index,tile in enumerate(expected_tiles):
    positions = [0,41,42,43,44]
    for slot,label in enumerate(tile):
        for bit in range(10):
            if ((label+512)>>bit)&1:
                positions.append(1+10*slot+bit)
    c[index] = sum(A**j for j in positions)
for slot in range(4):
    for bit in range(10):
        c[copy[slot][bit]] = A**(1+10*slot+bit)
for j,e in enumerate(anchors):
    c[e] = A**(41+j)
for e in dummies:
    c[e] = 0
assert set(c)==E
mu = (A-2) + sum((A-3)*A**j for j in range(1,45))
assert mu.bit_count()==405 and mu.bit_length()==450
mu += ((1<<78)-1)<<450
assert mu.bit_count()==483 and mu.bit_length()==528
assert [x for x in range(k+1) if not x & (A-2)] == [0,1]
assert [x for x in range(A) if not x & (A-3)] == [0,2]
# Exhaust every one-clause tile/copy bit pairing, including the occupancy bit.
clause_checks = 0
for tile in expected_tiles:
    for label in tile:
        assert 512 <= label+512 <= 950
        for bit in range(10):
            value = ((label+512)>>bit)&1
            for supplied in (0,1):
                assert (not ((value+supplied) & (A-3))) == (value==supplied)
                clause_checks += 1
# Raw coefficient sums, before selector decoding, never carry between A digits.
raw_sum = sum(c.values())
assert raw_sum < A**45
assert all((raw_sum//A**j)%A <= k+1 for j in range(45))
assert max((raw_sum//A**j)%A for j in range(45)) == 944
assert raw_sum >> 450 == 0

b, L = 625, 78125
rho = 1 << b
d = b*L
assert d == 5**11
mass = (len(E)+2)*(2*raw_sum+6)
threshold = max(4*mass+8,2*mu+4,16)
assert threshold <= rho and threshold > (1<<125)
assert T2+2*max(E)+2 <= L and T2+2*max(E)+2 > L//5
assert mass <= rho//4-2
assert 3*rho//4+mass <= rho-2
assert rho//2+1+mass <= rho-2
assert 2*mu+4 <= rho
assert 0 < T1 < T2 < L
assert T2-T1 > 2*max(E)
assert L-(T2-T1) > max(E)
assert T2+max(E) < L

# Exact sparse convolution: test ALL native source basis vectors and all targets.
bare = (30,H+20,3*M,7*M)
DC = Counter({x:1 for x in bare})
for e,value in c.items():
    if value:
        DC[T1-e] += value
        DC[T2-e] += value
DR = {H:1}
vertical = [(copy[1][j],copy[3][j],copy[1][j]) for j in range(10)]
horizontal = [(H+copy[0][j],copy[2][j],copy[0][j]) for j in range(10)]
anchor_tests = [(anchors[2],anchors[0],anchors[2]),(anchors[3],anchors[1],anchors[3])]
targets = vertical + horizontal + anchor_tests
checks = 0
for target,unshifted,neighbor in targets:
    for e in E:
        assert DC.get(target-e,0)==int(e==unshifted)
        if target in {t[0] for t in horizontal}:
            assert DR.get(target-e,0)==int(e==neighbor)
            assert int(target==e)==0
        else:
            assert DR.get(target-e,0)==0
            assert int(target==e)==int(e==neighbor)
        checks += 3
for target in (T1,T2):
    for e in E:
        assert DC.get(target-e,0)==c[e]
        assert DR.get(target-e,0)==0
        checks += 2
# All nonzero monomials are strictly within their cell even after native input.
assert max(DC)+max(E) < L and H+max(E) < L
assert min(DC)>2 and H>2
assert all(DC.get(target-e,0)==0 for e in dummies for target,_,_ in targets)
assert all(DR.get(target-e,0)==0 for e in dummies for target,_,_ in targets)

# Exhaust the potential radix-rotation offsets, not only a distance estimate.
E_star = E | {dummies[0]+1}
contaminate1 = {(T1-e)%L for e in E_star}
contaminate2 = {(T2-e)%L for e in E_star}
assert not (contaminate1 & contaminate2)
anchor_rotations = {(anchors[2]-e)%L for e in E} & {(anchors[3]-e)%L for e in E}
assert anchor_rotations == {0}
assert [(e,f) for e in E for f in E if f-e==5*M] == [(4*M,9*M)]
assert all(e<M for e in E-set(anchors))
assert L > 2*max(E)
# For each nonzero within-digit bit shift, odd-support argument is exact:
# shifts 1..b-2 are even; shift b-1 spills only the first dummy upper bit.
for shift in range(1,b-1):
    assert ((1<<shift)&1)==0 and ((2<<shift)&1)==0
assert (1<<(b-1))%rho == rho//2
assert ((2<<(b-1))//rho)==1
assert anchors[2] != anchors[3]

# Exact mask bit positions, including native low-bit surplus.
field_bits = {2}
for target,_,_ in targets:
    assert b*target not in field_bits
    field_bits.add(b*target)
mu_bits = [j for j in range(mu.bit_length()) if (mu>>j)&1]
for target in (T1,T2):
    for j in mu_bits:
        assert b*target+j not in field_bits
        field_bits.add(b*target+j)
cleared_bits = {b*e for e in E if e!=1} | {b*dummies[0]+1}
assert len(cleared_bits)==989 and len(field_bits)==989
assert max(field_bits)<d-1 and max(cleared_bits)<d-1
assert cleared_bits & {0,1,2,3} == {0}
assert field_bits & set(range(8)) == {2}
assert len(field_bits)+(d-len(cleared_bits))==d
DC_mod5 = sum(value*pow(2,exponent,5) for exponent,value in DC.items())%5
DR_mod5 = pow(2,H,5)
assert (T2-T1)%4==2
assert (2*DC_mod5-DR_mod5)%5==4
# Every dyadic base is 2 modulo 5 because its exponent is a power of five.
assert b%4==L%4==d%4==1

expected_scalar = dict(k=k,a=bits,ell=10,A=A,dummy_count=2,e_star=dummies[0],M=M,
    Emax=max(E),Hc=H,T1=T1,T2=T2,gap=T2-T1,b=b,L=L,d=d,native_support=len(E),
    clause_digits=44,mu_population=mu.bit_count(),mu_bit_length=mu.bit_length(),
    mass_bit_length=mass.bit_length(),threshold_bit_length=threshold.bit_length(),
    copy_offsets=[block[0] for block in copy],anchors=anchors,bare_shifts=list(bare))
assert json.loads((BASE/'wang943_layout.json').read_text()) == expected_scalar

receipt = dict(status='PASS',scope='Independent finite checks; mathematical global proof is in the companion audit, not machine-certified',
    source_sha256=HASH,tile_count=len(expected_tiles),tile_sha256=sha256((BASE/'wang943_tiles.json').read_bytes()).hexdigest(),
    group_counts={name:len(tiles) for name,tiles in group.items()},
    right_targets=len(right_targets),left_targets=len(left_targets),
    binary_clause_pair_checks=clause_checks,basis_convolution_checks=checks,
    raw_base_A_digit_max=944,raw_clause_bit_length=raw_sum.bit_length(),
    dense_padding_start_bit=450,dense_padding_bits=78,mu_population=483,
    field_mask_population=len(field_bits),data_mask_population=d-len(cleared_bits),
    anchor_rotations=sorted(anchor_rotations),mod5_unit=4,
    mass_bit_length=mass.bit_length(),threshold_bit_length=threshold.bit_length(),
    b=b,L=L,d=d,coefficient_bit_lengths={'beta':d,'K':b*(L+H)+1,'MC':d,'MF_source':d+1})
(ROOT/'audit/WANG943_INDEPENDENT_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))

# Optional byte-for-byte check of independently materialized fixed coefficients.
if (BASE/'coefficients').is_dir():
    import gzip
    def set_bit(output, position):
        output[position//8] |= 1 << (position%8)
    def or_term(output, value, bit_offset):
        byte_offset, remainder = divmod(bit_offset,8)
        value <<= remainder
        chunk = value.to_bytes((value.bit_length()+7)//8,'little')
        for offset,byte in enumerate(chunk):
            output[byte_offset+offset] |= byte
    expected_beta = bytearray([255])*((d+7)//8)
    expected_beta[-1] &= (1<<(d%8 or 8))-1
    expected_MC = bytearray(expected_beta)
    for position in cleared_bits:
        expected_MC[position//8] &= 255 ^ (1<<(position%8))
    K_bits = b*(L+H)+1
    expected_K = bytearray((K_bits+7)//8)
    for exponent,value in DC.items():
        or_term(expected_K,value,b*exponent)
    set_bit(expected_K,d+b*H)
    expected_MF_source = bytearray((d+1+7)//8)
    for position in (field_bits-{2}) | {0,1,d}:
        set_bit(expected_MF_source,position)
    binaries = {}
    for name,expected in [('beta',expected_beta),('K',expected_K),('MC',expected_MC),('MF_source',expected_MF_source)]:
        file = BASE/'coefficients'/f'{name}.bin'
        actual = file.read_bytes()
        assert actual == expected, f'Coefficient mismatch: {name}'
        compressed = Path(str(file)+'.gz')
        assert gzip.decompress(compressed.read_bytes())==actual
        binaries[name] = {'bytes':len(actual),'sha256':sha256(actual).hexdigest(),
            'gzip_bytes':compressed.stat().st_size,'gzip_sha256':sha256(compressed.read_bytes()).hexdigest()}
    receipt['materialized_coefficients'] = binaries
    receipt['materialized_total_bytes'] = sum(row['bytes'] for row in binaries.values())
    receipt['compressed_total_bytes'] = sum(row['gzip_bytes'] for row in binaries.values())
    (ROOT/'audit/WANG943_INDEPENDENT_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'materialized_coefficients':binaries},indent=2))
