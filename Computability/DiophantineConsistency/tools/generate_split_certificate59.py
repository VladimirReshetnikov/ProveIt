#!/usr/bin/env python3
"""Generate a Lean certificate from report59's authoritative old-z source.

Only inert, SHA-pinned JSON is read. Arithmetic identities and finite support
certificates in the generated file are independently checked by the Lean kernel.
"""
from pathlib import Path
from collections import defaultdict
from itertools import combinations_with_replacement
import ast
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data/split59'
OUTPUT = ROOT / 'Lean/DiophantineConsistency/SplitCertificate59.lean'
PINS = {
    'parent_source.json': '1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287',
    'split_code.json': 'abbedad94a3e619d71d61551c9cd76db5dd9ec35e67bd8382a18deb90fb8f38e',
    'split_kernels.json': '445de50798fe3c22a195d9e643b5684f0224c7130b56a316bcb29681a58dd02a',
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def add(a, b, scale=1):
    out = dict(a)
    for m, c in b.items():
        out[m] = out.get(m, 0) + scale * c
    return {m: c for m, c in out.items() if c}


def mul(a, b):
    out = defaultdict(int)
    for ma, ca in a.items():
        for mb, cb in b.items():
            out[tuple(x+y for x, y in zip(ma, mb))] += ca*cb
    return {m: c for m, c in out.items() if c}


def parse(text, names, abbreviations=None):
    z = (0,)*len(names)
    def visit(t):
        if isinstance(t, ast.Constant) and type(t.value) is int:
            return {z: t.value} if t.value else {}
        if isinstance(t, ast.Name):
            if abbreviations and t.id in abbreviations:
                return abbreviations[t.id]
            require(t.id in names, 'unknown scalar name '+t.id)
            return {tuple(int(i == names.index(t.id)) for i in range(len(names))): 1}
        if isinstance(t, ast.UnaryOp) and isinstance(t.op, ast.USub):
            return {m: -c for m, c in visit(t.operand).items()}
        if isinstance(t, ast.BinOp):
            a = visit(t.left)
            if isinstance(t.op, ast.Pow):
                require(isinstance(t.right, ast.Constant) and type(t.right.value) is int,
                        'nonliteral exponent')
                require(0 <= t.right.value <= 4, 'unexpected exponent')
                out = {z: 1}
                for _ in range(t.right.value): out = mul(out, a)
                return out
            b = visit(t.right)
            if isinstance(t.op, ast.Add): return add(a, b)
            if isinstance(t.op, ast.Sub): return add(a, b, -1)
            if isinstance(t.op, ast.Mult): return mul(a, b)
        raise ValueError(ast.dump(t))
    return visit(ast.parse(text.replace('^', '**'), mode='eval').body)


def grouping(poly):
    result = defaultdict(dict)
    for m, c in sorted(poly.items()):
        result[m[:31]][m[31:]] = c
    return dict(result)


def monomial(m, atom):
    return ' * '.join(atom(i)+(f' ^ {e}' if e > 1 else '')
                      for i, e in enumerate(m) if e) or '1'


def coefficient(poly):
    terms = []
    for m, c in sorted(poly.items()):
        term = monomial(m, lambda i: f'ports {i}')
        if term == '1': term = str(c)
        elif c == -1: term = f'(-({term}))'
        elif c != 1: term = f'({c}) * {term}'
        terms.append(term)
    return '('+' + '.join(terms)+')' if terms else '0'


def expression(poly):
    terms = []
    for m, p in sorted(grouping(poly).items()):
        coeff = coefficient(p)
        term = monomial(m, lambda i: f'x {i}')
        if term == '1': terms.append(coeff)
        elif coeff == '(1)': terms.append(term)
        else: terms.append(f'{coeff} * ({term})')
    return '('+' + '.join(terms)+')' if terms else '0'


def vec(values):
    return '!['+',\n    '.join(values)+']'


def fset(values):
    return '{'+', '.join(map(str, values))+'}' if values else '∅'


def pairlit(pair):
    return f'⟨({pair[0]}, {pair[1]}), by decide⟩'


def function(entries, var='i'):
    return '(fun '+var+' => '+''.join(f'if {var} = {k} then {v} else '
                                     for k, v in entries)+'0)'


def main():
    docs = {}
    for name, sha in PINS.items():
        raw = (DATA/name).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == sha, 'input pin '+name)
        docs[name] = json.loads(raw)
    source, code, kernels = (docs[n] for n in PINS)
    names = source['sparse_term_coordinate_order']
    require(len(source['variables']) == 31 and names[-4:] == ['beta','K0','MC','MF'],
            'variable/port order')
    abbreviations = {}
    for name,text in source['affine_abbreviations'].items():
        abbreviations[name] = parse(text,names,abbreviations)
    rows = []
    for i, eq in enumerate(source['equations']):
        require(eq['number'] == i+1, 'source row order')
        row = defaultdict(int)
        for t in eq['terms']: row[tuple(t['powers'])] += t['coefficient']
        row = {m: c for m, c in row.items() if c}
        require(row == parse(eq['residual'], names,abbreviations), 'source text/terms mismatch')
        rows.append(row)
    require(len(rows) == 22, 'source row count')
    # This residual is old-z, with the extra beta*J term relative to report52.
    require(parse('(K0+w)*(beta*J+1-F-alpha)+(beta*J+1-F)-z*beta*J-1', names)
            == rows[14], 'authoritative old-z transport')
    transformed = list(rows)
    require(code['source_row_operations'] == [[14,2,1],[15,3,1]], 'row operations')
    for target, donor, scale in code['source_row_operations']:
        transformed[target-1] = add(transformed[target-1], transformed[donor-1], scale)
    order = [k-1 for k in code['order']]
    require(sorted(order) == list(range(22)), 'row permutation')
    delivered = [transformed[k] for k in order]
    w, E = code['weights'], code['targets']
    require(len(w) == 31 and len(set(w)) == 31 and min(w)>0 and max(w)==116, 'weights')
    require(len(E) == 22 and len(set(E)) == 22 and max(E)==2129, 'targets')
    constants, linear, quadratic = [], [], []
    for row in delivered:
        a0, a1, a2 = {}, {}, {}
        for m, p in grouping(row).items():
            deg = sum(m)
            require(deg <= 2, 'nonquadratic source')
            if deg == 0: a0 = p
            elif deg == 1: a1[m.index(1)] = p
            else:
                pair = tuple(i for i, e in enumerate(m) for _ in range(e))
                a2[pair] = p
        constants.append(a0); linear.append(a1); quadratic.append(a2)
    require((sum(bool(x) for x in constants),sum(map(len,linear)),sum(map(len,quadratic)))
            == (7,39,43), '89 degree-separated records')
    pairs = sorted({p for row in quadratic for p in row})
    require(len(pairs) == 39, 'active pair count')
    allpairs = list(combinations_with_replacement(range(31),2))
    for p in pairs:
        require([q for q in allpairs if w[q[0]]+w[q[1]] == w[p[0]]+w[p[1]]] == [p],
                'active quadratic isolation')
    expected = [defaultdict(dict) for _ in range(3)]
    for k in range(22):
        if constants[k]:
            expected[0][E[k]] = {m:2*c for m,c in constants[k].items()}
        for i,p in linear[k].items():
            require(w[i] <= E[k], 'linear exponent negative')
            for l in range(22):
                if k != l:
                    require(all(w[j]+E[k]-w[i] != E[l] for j in range(31)), 'linear cross')
            require(E[k]-w[i] not in expected[1], 'duplicate linear coefficient exponent')
            expected[1][E[k]-w[i]] = {m:2*c for m,c in p.items()}
        for (i,j),p in quadratic[k].items():
            require(w[i]+w[j] <= E[k], 'quadratic exponent negative')
            for l in range(22):
                if k != l:
                    require(all(w[a]+w[b]+E[k]-w[i]-w[j] != E[l]
                                for a,b in allpairs), 'quadratic cross')
            pos = E[k]-w[i]-w[j]
            require(pos not in expected[2], 'duplicate quadratic coefficient exponent')
            expected[2][pos] = {m:(2 if i==j else 1)*c for m,c in p.items()}
    for channel in kernels['kernels']:
        actual = {t['exponent']:{tuple(v['powers']):v['coefficient'] for v in t['coefficient']}
                  for t in channel['terms']}
        require(actual == expected[channel['degree']], 'literal kernel mismatch')
    s2 = [[pairs.index(p) for p in sorted(row)] for row in quadratic]
    a0 = [coefficient(p) for p in constants]
    a1 = [function([(i,coefficient(p)) for i,p in sorted(row.items())]) for row in linear]
    a2 = [function([(pairlit(i),coefficient(p)) for i,p in sorted(row.items())], 'p')
          for row in quadratic]
    out = ['''import DiophantineConsistency.DegreeSeparatedCoding
import Mathlib.Data.Fin.VecNotation

/-!
# The authoritative report59 split116 source and channel certificate

Generated by tools/generate_split_certificate59.py from SHA-pinned inert JSON.
Parent SHA256 1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287.
The source uses the OLD positive transport coordinate. It is independently
transcribed from that parent, without using report52's shifted row15.
All coefficient ports remain parameters; no native calibration is claimed.
-/

namespace DiophantineConsistency.SplitCertificate59

open Polynomial SidonPositions SelectiveQuadraticCoding DegreeSeparatedCoding
open scoped BigOperators

set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 512

variable {R : Type*} [CommRing R]
''']
    out.append('/-- Original31 source, with literal old-z transport. -/\ndef sourceRows (ports : Fin 4 → R) (x : Fin 31 → R) : Fin 22 → R :=\n  '+vec([expression(p) for p in rows])+'\n')
    out.append('/-- Exactly rho14=r14+r2 and rho15=r15+r3, in original order. -/\ndef transformedRows (ports : Fin 4 → R) (x : Fin 31 → R) : Fin 22 → R :=\n  '+vec([expression(p) for p in transformed])+'\n')
    out.append('def rowOrder : Fin 22 → Fin 22 := '+vec(list(map(str,order)))+'\n')
    out.append('theorem rowOrder_surjective : Function.Surjective rowOrder := by decide\n')
    out.append('def deliveredRows (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) : R :=\n  transformedRows ports x (rowOrder k)\n')
    out.append('def weights : Fin 31 → ℕ := '+vec(list(map(str,w)))+'\n')
    out.append('def targets : Fin 22 → ℕ := '+vec(list(map(str,E)))+'\n')
    out.append('theorem weights_injective : Function.Injective weights := by decide\n')
    out.append('theorem maximum_weight : ∀ i, weights i ≤ 116 := by decide\n')
    out.append('theorem weights_positive : ∀ i, 0 < weights i := by decide\n')
    out.append('theorem targets_injective : Function.Injective targets := by decide\n')
    out.append('def activePair : Fin 39 → PairIndex 30 :=\n  '+vec(list(map(pairlit,pairs)))+'\n')
    out.append('theorem active_isolated : ∀ i, Isolated weights (activePair i) := by\n  unfold Isolated\n  decide\n')
    out.append('def linearSupport : Fin 22 → Finset (Fin 31) :=\n  '+vec([fset(sorted(p)) for p in linear])+'\n')
    out.append('def quadraticIndices : Fin 22 → Finset (Fin 39) :=\n  '+vec([fset(p) for p in s2])+'\n')
    out.append('def quadraticSupport (k : Fin 22) : Finset (PairIndex 30) :=\n  (quadraticIndices k).image activePair\n')
    out.append('def constantCoefficient (ports : Fin 4 → R) : Fin 22 → R :=\n  '+vec(a0)+'\n')
    out.append('def linearCoefficient (ports : Fin 4 → R) : Fin 22 → Fin 31 → R :=\n  '+vec(a1)+'\n')
    out.append('def quadraticCoefficient (ports : Fin 4 → R) : Fin 22 → PairIndex 30 → R :=\n  '+vec(a2)+'\n')
    out.append('''/-- A cross target is isolated globally if nearby targets are isolated. -/
theorem target_cross_of_near {t u a b d : ℕ} (ha : a ≤ d) (hb : b ≤ d)
    (near : t ≤ u + d → u ≤ t + d → b + (t - a) ≠ u) :
    b + (t - a) ≠ u := by
  by_cases h : t ≤ u + d
  · by_cases h' : u ≤ t + d
    · exact near h h'
    · intro he
      have hs := Nat.sub_le t a
      omega
  · intro he
    omega
''')
    out.append('''theorem linear_span : ∀ k i, i ∈ linearSupport k → weights i ≤ targets k := by decide

private theorem linear_cross_near : ∀ k l, k ≠ l →
    targets k ≤ targets l+116 → targets l ≤ targets k+116 →
    ∀ i ∈ linearSupport k, ∀ j,
      weights j + (targets k - weights i) ≠ targets l := by decide

theorem linear_cross (k l : Fin 22) (hkl : k ≠ l) (i : Fin 31)
    (hi : i ∈ linearSupport k) (j : Fin 31) :
    weights j + (targets k - weights i) ≠ targets l := by
  exact SplitCertificate59.target_cross_of_near (maximum_weight i) (maximum_weight j)
    (fun h1 h2 => linear_cross_near k l hkl h1 h2 i hi j)

private theorem quadratic_span_indices : ∀ k i, i ∈ quadraticIndices k →
    pairWeight weights (activePair i) ≤ targets k := by decide

private theorem quadratic_cross_near : ∀ k l, k ≠ l →
    targets k ≤ targets l+232 → targets l ≤ targets k+232 →
    ∀ a ∈ quadraticIndices k, ∀ i j : Fin 31,
      weights i + weights j + (targets k - pairWeight weights (activePair a)) ≠
        targets l := by decide

private theorem quadratic_cross_indices (k l : Fin 22) (hkl : k ≠ l)
    (a : Fin 39) (ha : a ∈ quadraticIndices k) (i j : Fin 31) :
    weights i + weights j + (targets k - pairWeight weights (activePair a)) ≠
      targets l := by
  have hw1 := maximum_weight (activePair a).val.1
  have hw2 := maximum_weight (activePair a).val.2
  have hwi := maximum_weight i
  have hwj := maximum_weight j
  have hp : pairWeight weights (activePair a) ≤ 232 := by
    dsimp only [SelectiveQuadraticCoding.pairWeight]
    omega
  have hb : weights i + weights j ≤ 232 := by omega
  exact SplitCertificate59.target_cross_of_near hp hb
    (fun h1 h2 => quadratic_cross_near k l hkl h1 h2 a ha i j)

theorem quadratic_span (k : Fin 22) (p : PairIndex 30) (hp : p ∈ quadraticSupport k) :
    pairWeight weights p ≤ targets k := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
  exact quadratic_span_indices k a ha

theorem quadratic_isolated (k : Fin 22) (p : PairIndex 30) (hp : p ∈ quadraticSupport k) :
    Isolated weights p := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
  exact active_isolated a

theorem quadratic_cross (k l : Fin 22) (hkl : k ≠ l) (p : PairIndex 30)
    (hp : p ∈ quadraticSupport k) (i j : Fin 31) :
    weights i + weights j + (targets k - pairWeight weights p) ≠ targets l := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
  exact quadratic_cross_indices k l hkl a ha i j
''')
    for k in range(22):
        rhs = f'sourceRows ports x {k}'
        if k == 13: rhs += ' + sourceRows ports x 1'
        elif k == 14: rhs += ' + sourceRows ports x 2'
        scalar_rhs = expression(rows[k])
        if k in (13,14): scalar_rhs += ' + '+expression(rows[1 if k == 13 else 2])
        proof = 'change '+expression(transformed[k])+' = '+scalar_rhs+'\n  '+('ring' if k in (13,14) else 'rfl')
        out.append(f'private theorem transformed_row{k} (ports : Fin 4 → R) (x : Fin 31 → R) :\n    transformedRows ports x {k} = {rhs} := by\n  '+proof+'\n')
    out.append('''theorem transformed_zero_iff (ports : Fin 4 → R) (x : Fin 31 → R) :
    (∀ k, transformedRows ports x k = 0) ↔ ∀ k, sourceRows ports x k = 0 := by
  constructor
  · intro h
    have h1 : sourceRows ports x 1 = 0 := (transformed_row1 ports x).symm.trans (h 1)
    have h2 : sourceRows ports x 2 = 0 := (transformed_row2 ports x).symm.trans (h 2)
    intro k
    fin_cases k
''')
    for k in range(22):
        if k in (13,14):
            out.append(f'    · change sourceRows ports x {k} = 0\n      have hh := (transformed_row{k} ports x).symm.trans (h {k})\n      simpa only [h{1 if k==13 else 2}, add_zero] using hh\n')
        else: out.append(f'    · change sourceRows ports x {k} = 0\n      exact (transformed_row{k} ports x).symm.trans (h {k})\n')
    out.append('  · intro h k\n    fin_cases k\n')
    for k in range(22):
        out.append(f'    · change transformedRows ports x {k} = 0\n      rw [transformed_row{k}]\n      simp only [h, add_zero]\n')
    out.append('''theorem delivered_zero_iff (ports : Fin 4 → R) (x : Fin 31 → R) :
    (∀ k, deliveredRows ports x k = 0) ↔ ∀ k, sourceRows ports x k = 0 := by
  rw [← transformed_zero_iff]
  constructor
  · intro h k
    obtain ⟨l,rfl⟩ := rowOrder_surjective k
    exact h l
  · intro h k
    exact h (rowOrder k)
''')
    for k in range(22):
        ps = [pairlit(pairs[i]) for i in s2[k]]
        out.append(f'''private theorem rowIdentity_{k} (ports : Fin 4 → R) (x : Fin 31 → R) :
    value (constantCoefficient ports {k}) (linearSupport {k}) (linearCoefficient ports {k})
      (quadraticSupport {k}) (quadraticCoefficient ports {k}) x = deliveredRows ports x {k} := by
  have hs1 : linearSupport {k} = {fset(sorted(linear[k]))} := rfl
  have hs2 : quadraticSupport {k} = {fset(ps)} := by decide
  have ha0 : constantCoefficient ports {k} = {a0[k]} := rfl
  have ha1 : linearCoefficient ports {k} = {a1[k]} := by unfold linearCoefficient; rfl
  have ha2 : quadraticCoefficient ports {k} = {a2[k]} := by unfold quadraticCoefficient; rfl
  have hsource : deliveredRows ports x {k} = {expression(delivered[k])} := by
    unfold deliveredRows transformedRows rowOrder
    rfl
  rw [hs1,hs2,ha0,ha1,ha2,hsource]
  simp [value, linearValue, rowValue]
  <;> ring
''')
    out.append('''theorem rowValue_eq_source (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) :
    value (constantCoefficient ports k) (linearSupport k) (linearCoefficient ports k)
      (quadraticSupport k) (quadraticCoefficient ports k) x = deliveredRows ports x k := by
  fin_cases k
''')
    out.extend(f'  · exact rowIdentity_{k} ports x\n' for k in range(22))
    out.append('''/-- Full same-degree extraction at all22 literal targets. -/
theorem coeff_source_rows (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) :
    (product weights x (constantCoefficient ports) linearSupport (linearCoefficient ports)
      quadraticSupport (quadraticCoefficient ports) targets).coeff (targets k) =
        2 * deliveredRows ports x k := by
  rw [coeff_product weights weights_injective x (constantCoefficient ports)
    linearSupport (linearCoefficient ports) quadraticSupport (quadraticCoefficient ports)
    targets targets_injective linear_span linear_cross quadratic_span quadratic_isolated
    quadratic_cross k, rowValue_eq_source]

/-- These target coefficients vanish exactly at the authoritative old-z source zeros. -/
theorem coeff_zero_iff_source_zero (ports : Fin 4 → ℤ) (x : Fin 31 → ℤ) :
    (∀ k, (product weights x (constantCoefficient ports) linearSupport (linearCoefficient ports)
      quadraticSupport (quadraticCoefficient ports) targets).coeff (targets k) = 0) ↔
        ∀ k, sourceRows ports x k = 0 := by
  rw [← delivered_zero_iff]
  constructor
  · intro h k
    have hh := h k
    rw [coeff_source_rows] at hh
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num : (2 : ℤ) ≠ 0)
  · intro h k
    rw [coeff_source_rows,h k,mul_zero]

end DiophantineConsistency.SplitCertificate59
''')
    geometry_starts = (
        'def weights ', 'def targets ', 'theorem weights_injective ',
        'theorem maximum_weight ', 'theorem weights_positive ',
        'theorem targets_injective ', 'def activePair ',
        'theorem active_isolated ', 'def linearSupport ',
        'def quadraticIndices ', 'def quadraticSupport ', '/-- A cross target ', 'theorem linear_span ')
    geometry_items = [t for t in out[1:] if t.startswith(geometry_starts)]
    parent_items = [t for t in out[1:] if not t.startswith(geometry_starts)]
    geometry_header = out[0].replace(
        '# The authoritative report59 split116 source and channel certificate',
        '# Literal report59 split116 weight and target geometry')
    geometry_extra = """
/-- The31 actual input positions; there is no dummy coordinate. -/
def inputPositions : Finset ℕ := Finset.univ.image weights

def targetPositions : Finset ℕ := Finset.univ.image targets

theorem inputPositions_card : inputPositions.card = 31 := by decide

theorem targetPositions_card : targetPositions.card = 22 := by decide

theorem inputPositions_range : inputPositions ⊆ Finset.range 117 := by decide

theorem maximum_target : ∀ k, targets k ≤ 2129 := by decide

theorem targetPositions_range : targetPositions ⊆ Finset.range 2162 := by decide

theorem inputPositions_zero : 0 ∉ inputPositions := by decide

end DiophantineConsistency.SplitCertificate59
"""
    geometry_file = OUTPUT.with_name('SplitGeometry59.lean')
    geometry_file.write_text('\n'.join([geometry_header]+geometry_items+[geometry_extra]))
    parent_header = out[0].replace('import DiophantineConsistency.DegreeSeparatedCoding',
                                 'import DiophantineConsistency.SplitGeometry59')
    geometry_text = '\n'.join([geometry_header]+geometry_items+[geometry_extra])
    geometry_file.write_text(geometry_text.replace('by decide', 'by decide +kernel').replace('  decide\n', '  decide +kernel\n'))
    OUTPUT.write_text('\n'.join([parent_header]+parent_items).replace('by decide', 'by decide +kernel'))
    print(json.dumps({'status':'GENERATED','input_sha256':PINS,
        'records':89,'channels':[7,39,43],'active_pairs':39,
        'same_degree_interactions':43*496+39*31+7,
        'output':str(OUTPUT.relative_to(ROOT))},sort_keys=True))


if __name__ == '__main__':
    main()
