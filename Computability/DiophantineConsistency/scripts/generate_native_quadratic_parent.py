#!/usr/bin/env python3
"""Emit the port-parametric Lean source and independently check the row expansion.

Run from any directory. Only Python's standard library is used. The emitted
Lean proof checks the extraction identities; this script is not trusted by it.
"""
from pathlib import Path
import ast
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'data/native-quadratic52/source_system60.json'
CERT = ROOT / 'con-zfc-diophantine-forms/52-sparse-pell/packing/CERTIFICATE_174_interior_regular.json'
OUTPUT = ROOT / 'Lean/DiophantineConsistency/NativeQuadraticParent.lean'
SOURCE_SHA = 'ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48'
CERT_SHA = 'c1740ad4de5142143ee7282a8229fe6e76e26a74128846cba9b2212e1b27033c'

def require(ok, message):
    if not ok:
        raise ValueError(message)


def poly_add(a, b, sign=1):
    out = dict(a)
    for exponent, coefficient in b.items():
        out[exponent] = out.get(exponent, 0) + sign * coefficient
    return {e: c for e, c in out.items() if c}


def poly_mul(a, b):
    out = {}
    for ea, ca in a.items():
        for eb, cb in b.items():
            exponent = tuple(x + y for x, y in zip(ea, eb))
            out[exponent] = out.get(exponent, 0) + ca * cb
    return {e: c for e, c in out.items() if c}


def polynomial(text, names):
    n = len(names)
    def literal(k):
        return {(0,) * n: k} if k else {}
    def visit(t):
        if isinstance(t, ast.Constant) and type(t.value) is int:
            return literal(t.value)
        if isinstance(t, ast.Name):
            return {tuple(int(i == names.index(t.id)) for i in range(n)): 1}
        if isinstance(t, ast.UnaryOp) and isinstance(t.op, ast.USub):
            return {e: -c for e, c in visit(t.operand).items()}
        if isinstance(t, ast.BinOp):
            a = visit(t.left)
            if isinstance(t.op, ast.Pow):
                require(isinstance(t.right, ast.Constant) and type(t.right.value) is int,
                        'nonliteral exponent')
                require(0 <= t.right.value <= 4, 'exponent outside finite source')
                out = literal(1)
                for _ in range(t.right.value):
                    out = poly_mul(out, a)
                return out
            b = visit(t.right)
            if isinstance(t.op, ast.Add): return poly_add(a, b)
            if isinstance(t.op, ast.Sub): return poly_add(a, b, -1)
            if isinstance(t.op, ast.Mult): return poly_mul(a, b)
        raise ValueError(ast.dump(t))
    return visit(ast.parse(text, mode='eval').body)


def lean_coefficient(text, ports):
    def visit(t):
        if isinstance(t, ast.Constant) and type(t.value) is int: return str(t.value)
        if isinstance(t, ast.Name): return f'ports {ports.index(t.id)}'
        if isinstance(t, ast.UnaryOp) and isinstance(t.op, ast.USub):
            return f'(-{visit(t.operand)})'
        if isinstance(t, ast.BinOp):
            if isinstance(t.op, ast.Pow):
                return f'({visit(t.left)} ^ {t.right.value})'
            op = {ast.Add: '+', ast.Sub: '-', ast.Mult: '*'}[type(t.op)]
            return f'({visit(t.left)} {op} {visit(t.right)})'
        raise ValueError(ast.dump(t))
    return visit(ast.parse(text, mode='eval').body)


def pair(alpha):
    require(sum(alpha) <= 2, 'source row not quadratic')
    indices = [0] * (2 - sum(alpha))
    indices += [i + 1 for i, e in enumerate(alpha) for _ in range(e)]
    require(len(indices) == 2, 'wrong padded pair size')
    return tuple(indices)


def pair_literal(p):
    return f'⟨({p[0]}, {p[1]}), by decide⟩'


def main():
    require(hashlib.sha256(SOURCE.read_bytes()).hexdigest() == SOURCE_SHA, 'source pin')
    require(hashlib.sha256(CERT.read_bytes()).hexdigest() == CERT_SHA, 'certificate pin')
    source = json.loads(SOURCE.read_text())
    cert = json.loads(CERT.read_text())
    require(cert['source_sha256'] == SOURCE_SHA, 'certificate source pin')
    variables, ports = source['variables'], source['constants']
    require(len(variables) == 31 and ports == ['beta', 'K0', 'MC', 'MF'], 'coordinate order')
    names = variables + ports
    n = len(names)
    zero = (0,) * n
    def literal(k): return {zero: k} if k else {}
    env = {name: poly_add(polynomial(name, names), literal(1)) for name in variables}
    env.update({name: polynomial(name, names) for name in ports})
    def get(x): return literal(x) if type(x) is int else env[x]
    for name, op, a, b in source['source']:
        require(name not in env, 'duplicate source register')
        env[name] = {'+': lambda: poly_add(get(a), get(b)),
                     '-': lambda: poly_add(get(a), get(b), -1),
                     '*': lambda: poly_mul(get(a), get(b))}[op]()
    require(len(source['source']) == 60 and len(source['comparisons']) == 22, 'literal evaluator size')
    residuals = [poly_add(get(a), get(b), -1) for a, b in source['comparisons']]
    for row in cert['rows']:
        terms = {}
        for term in row['terms']:
            for exponent, coefficient in polynomial(term['coefficient'], ports).items():
                key = tuple(term['alpha']) + exponent
                require(key not in terms, 'duplicate sparse source term')
                terms[key] = coefficient
        require(terms == residuals[row['original_row_one_based'] - 1], 'source/certificate polynomial mismatch')
    require(cert['row_order_one_based'] == [r['original_row_one_based'] for r in cert['rows']], 'row order')

    def atom(a):
        if type(a) is int: return str(a)
        if a in variables: return f'x {variables.index(a)}'
        if a in ports: return f'ports {ports.index(a)}'
        return a

    out = '''import DiophantineConsistency.SelectiveCertificate52

/-!
# The literal native quadratic parent and its selected extraction

Generated by `scripts/generate_native_quadratic_parent.py` from the exact
60-gate source_system60.json, SHA256 SOURCE_HASH.
The original input order is J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,
N,E,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta. Ports are beta,K0,MC,MF.

The theorem below holds for arbitrary coefficient ports in any commutative
ring. It proves the literal source-to-coefficient identity, without claiming
that a native compiler or a consistency predicate has been encoded.
-/

namespace DiophantineConsistency.NativeQuadraticParent

open SidonPositions SelectiveQuadraticCoding
open scoped BigOperators

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

variable {R : Type*} [CommRing R]

/-- The exact 60 live binary arithmetic gates followed by their 22 residuals.
The original semantic domain is positive integer inputs. -/
def sourceRows (ports : Fin 4 → R) (x : Fin 31 → R) : Fin 22 → R :=
'''.replace('SOURCE_HASH', SOURCE_SHA)
    for name, op, a, b in source['source']:
        out += f'  let {name} : R := {atom(a)} {op} {atom(b)}\n'
    out += '  ![' + ',\n    '.join(f'{atom(a)} - {atom(b)}' for a, b in source['comparisons']) + ']\n\n'
    out += '/-- Delivered source row ordering, with the nonzero constant guard last. -/\n'
    out += 'def rowOrder : Fin 22 → Fin 22 := ![' + ', '.join(str(i - 1) for i in cert['row_order_one_based']) + ']\n\n'
    out += '/-- The delivered ordering is a permutation of all22 source rows. -/\n'
    out += 'theorem rowOrder_surjective : Function.Surjective rowOrder := by decide\n\n'
    out += '/-- Shift every original positive coordinate by one. -/\n'
    out += 'def shiftedRows (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) : R :=\n'
    out += '  sourceRows ports (fun i => x i + 1) (rowOrder k)\n\n'
    out += '/-- Homogeneous padding coordinate 0 is fixed to one, with weight 81. -/\n'
    out += 'def padded (x : Fin 31 → R) : Fin 32 → R := Fin.cases 1 x\n\n'
    active_pairs = sorted({pair(t['alpha']) for row in cert['rows'] for t in row['terms']})
    require(len(active_pairs) == 71, 'active pair count')
    out += '/-- Literal row support indices in the checked71-pair certificate. -/\n'
    out += 'def rowSupportIndices : Fin 22 → Finset (Fin 71) :=\n  !['
    out += ',\n    '.join('{' + ', '.join(str(active_pairs.index(pair(t['alpha']))) for t in r['terms']) + '}' for r in cert['rows']) + ']\n\n'
    out += '/-- The exact support, carried through the certified active-pair map. -/\n'
    out += 'def rowSupport (k : Fin 22) : Finset (PairIndex 31) :=\n'
    out += '  (rowSupportIndices k).image SelectiveCertificate52.activePair\n\n'
    out += '/-- Exact unweighted quadratic coefficients; zero away from a listed pair. -/\n'
    out += 'def rowCoefficient (ports : Fin 4 → R) : Fin 22 → PairIndex 31 → R :=\n  !['
    out += ',\n    '.join('(fun p => ' + ''.join(f"if p = {pair_literal(pair(t['alpha']))} then {lean_coefficient(t['coefficient'], ports)} else " for t in r['terms']) + '0)' for r in cert['rows']) + ']\n\n'
    out += '''/-- The actual source supports lie inside the kernel-checked selective support. -/
theorem rowSupport_subset : ∀ k p, p ∈ rowSupport k →
    p ∈ SelectiveCertificate52.activeSupport := by
  intro k p hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
'''
    out += '\nattribute [local irreducible] sourceRows shiftedRows rowCoefficient\n\n'
    exprs = {}
    def source_atom(a):
        if type(a) is int: return str(a)
        if a in variables: return f'(x {variables.index(a)} + 1)'
        if a in ports: return f'ports {ports.index(a)}'
        return exprs[a]
    for name, op, a, b in source['source']:
        exprs[name] = f'({source_atom(a)} {op} {source_atom(b)})'
    for i, row in enumerate(cert['rows']):
        coefficient = '(fun p => ' + ''.join(f"if p = {pair_literal(pair(t['alpha']))} then {lean_coefficient(t['coefficient'], ports)} else " for t in row['terms']) + '0)'
        a, b = source['comparisons'][row['original_row_one_based'] - 1]
        source_value = f'({source_atom(a)} - {source_atom(b)})'
        support = '{' + ', '.join(pair_literal(pair(t['alpha'])) for t in row['terms']) + '}'
        coordinates = sorted({v for t in row['terms'] for v in pair(t['alpha'])})
        out += f'''private theorem rowIdentity_{i} (ports : Fin 4 → R) (x : Fin 31 → R) :
    rowValue (rowSupport {i}) (rowCoefficient ports {i}) (padded x) = shiftedRows ports x {i} := by
  have hsupport : rowSupport {i} = {support} := by rfl
  have hcoefficient : rowCoefficient ports {i} = {coefficient} := by unfold rowCoefficient; rfl
  have hsource : shiftedRows ports x {i} = {source_value} := by unfold shiftedRows sourceRows rowOrder; rfl
  rw [hsupport, hcoefficient, hsource]
  unfold rowValue
  repeat' rw [Finset.sum_insert]
  rw [Finset.sum_singleton]
  all_goals first | decide | skip
'''
        for j in coordinates:
            rhs = '1' if j == 0 else f'x {j-1}'
            out += f'  have hp{j} : padded x {j} = {rhs} := rfl\n'
        out += '  norm_num ['
        out += ', '.join('hp'+str(j) for j in coordinates) + ']\n'
        out += '  try simp (config := { decide := true }) only [ite_false]\n'
        out += '  all_goals ring\n\n'
    out += '''/-- Exact equality with the literal60-gate source, for all port values.
This checks every constant, linear, diagonal, and off-diagonal coefficient
and the successor translation, with the complete4-port tuple retained. -/
theorem rowValue_eq_shiftedRows (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) :
    rowValue (rowSupport k) (rowCoefficient ports k) (padded x) = shiftedRows ports x k := by
  fin_cases k
'''
    for i in range(22):
        out += f'  · exact rowIdentity_{i} ports x\n'
    out += '''
/-- Selected coefficients recover twice the actual shifted source rows. -/
theorem coeff_source_rows (ports : Fin 4 → R) (x : Fin 31 → R) (k : Fin 22) :
    (encoded SelectiveCertificate52.weights (padded x) ^ 2 *
      combined SelectiveCertificate52.weights rowSupport (rowCoefficient ports)
        (fun j => 349 * (j.val + 1))).coeff (349 * (k.val + 1)) =
      2 * shiftedRows ports x k := by
  rw [SelectiveCertificate52.coeff_rows rowSupport (rowCoefficient ports) (padded x)
    rowSupport_subset k, rowValue_eq_shiftedRows]

/-- Vanishing of all selected coefficients is exactly the original22-row
source predicate on successor inputs, uniformly in the complete port tuple. -/
theorem target_zeros_iff_source_zeros (ports : Fin 4 → ℤ) (x : Fin 31 → ℤ) :
    (∀ k : Fin 22,
      (encoded SelectiveCertificate52.weights (padded x) ^ 2 *
        combined SelectiveCertificate52.weights rowSupport (rowCoefficient ports)
          (fun j => 349 * (j.val + 1))).coeff (349 * (k.val + 1)) = 0) ↔
      ∀ j, sourceRows ports (fun i => x i + 1) j = 0 := by
  constructor
  · intro h j
    obtain ⟨k, rfl⟩ := rowOrder_surjective j
    have hc : 2 * shiftedRows ports x k = 0 := by
      rw [← coeff_source_rows]
      exact h k
    simpa only [shiftedRows] using
      (mul_eq_zero.mp hc).resolve_left (by decide : (2 : ℤ) ≠ 0)
  · intro h k
    rw [coeff_source_rows, shiftedRows, h, mul_zero]

#print axioms rowSupport_subset
#print axioms rowValue_eq_shiftedRows
#print axioms coeff_source_rows
#print axioms target_zeros_iff_source_zeros

end DiophantineConsistency.NativeQuadraticParent
'''
    OUTPUT.write_text(out)
    print(json.dumps({'status': 'PASS', 'source_sha256': SOURCE_SHA, 'certificate_sha256': CERT_SHA,
                      'source_gates': 60, 'rows': 22, 'sparse_records': sum(len(r['terms']) for r in cert['rows']),
                      'output': str(OUTPUT.relative_to(ROOT))}, indent=2))

if __name__ == '__main__':
    main()
