#!/usr/bin/env python3
"""Lossless certificate packing and independent plain-bisim checker.

Research validation only: this Python program is NOT a Rocq proof/kernel check.
Uses only the Python standard library and immutable source snapshots.
"""
from validation_guard import ensure_safe_runtime, read_pinned_source, read_pinned_source_bytes
ensure_safe_runtime()

from pathlib import Path
from collections import Counter
import hashlib, json, re

HERE = Path(__file__).resolve().parent
SRC = HERE / 'snapshot/rocq/rocq-extension/coq/215'

def paths(s):
    if not s: return ()
    tokens = s.split(';')
    if any(x not in ('true', 'false') for x in tokens):
        raise ValueError('INVALID_BOOLEAN_TOKEN: ' + s)
    return tuple(x == 'true' for x in tokens)

def read_cert():
    text = read_pinned_source('Cert215Offsets.v')
    rows = re.findall(r'\(\[(.*?)\], \[(.*?)\], (-?\d+)%Z, (\d+)%N, (\d+)%N\)', text)
    assert len(rows) == 2240
    return [(paths(a), paths(b), int(z), int(j), int(k)) for a,b,z,j,k in rows]

def pack(p):
    n = 1
    for b in reversed(p): n = 2*n + b
    return n

def unpack(n):
    assert n >= 1
    p = []
    while n != 1:
        p.append(bool(n % 2)); n //= 2
    return tuple(p)

def inc(p):
    p = list(p)
    for i in range(len(p)-1,-1,-1):
        p[i] = not p[i]
        if p[i]: break
    return tuple(p)

def strip(b,k,p):
    p = list(p)
    while p and k:
        k -= p.pop() == b
    return tuple(p)

def brk(k,p): return inc(strip(False,k,p))
def cont(k,p): return strip(True,k,p)

def parse_edge(s):
    s = s.split()
    op = {'CN':'N','CI':'I','CD':'D','CB':'B','CC':'C','CH':'H',
          'ENode':'N','EInc':'I','EDecnz':'D','EBreak':'B','EContinue':'C','EHalt':'H'}[s[0]]
    return op, int(s[1]) if len(s)>1 else None

def read_prog(name):
    text = read_pinned_source(name)
    if name == 'Prog215.v':
        body = text.split('Definition p215_tab',1)[1].split('].',1)[0]
        nodes = [tuple(map(parse_edge,r)) for r in re.findall(r'\((C\w+(?: \d+)?), (C\w+(?: \d+)?)\)',body)]
        assert len(nodes) == 179
        return nodes, 178
    rows = re.findall(r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)',text)
    assert [int(i) for i,_,_ in rows] == list(range(487))
    return [(parse_edge(a),parse_edge(b)) for _,a,b in rows], 0

def site(prog,p):
    nodes,n = prog
    for i in range(len(nodes)+1):
        e = nodes[n][p[i] if i<len(p) else False]
        if e[0]!='N':
            return e, (p+(False,)*(i+1))[:i+1]
        n = e[1]
    raise AssertionError('walk fuel exhausted')

def segment(prog,p):
    counts = Counter()
    for n in range(1000):
        (op,r),q = site(prog,p)
        if op in ('D','H'): return counts,p,n
        if op=='I': counts[r]+=1; p=inc(q)
        elif op=='B': p=brk(r,q)
        elif op=='C': p=cont(r,q)
        else: raise AssertionError('unexpected edge')
    raise AssertionError('segment fuel exhausted')

def check(prog1,prog2,cert):
    branches=0; max_segment=0; halt_rows=0
    def branch(a,b,j):
        nonlocal branches,max_segment
        c1,p1,n1=segment(prog1,a); c2,p2,n2=segment(prog2,b)
        assert 0<=j<len(cert)
        q1,q2,_,_,_=cert[j]
        assert c1==c2 and p1==q1 and p2==q2, (branches,j)
        branches+=1; max_segment=max(max_segment,n1,n2)
    branch((),(),0)
    for a,b,z,j,k in cert:
        assert z==0
        (op1,r1),q1=site(prog1,a); (op2,r2),q2=site(prog2,b)
        if op1==op2=='H': halt_rows+=1; continue
        assert op1==op2=='D' and r1==r2
        branch(inc(q1),inc(q2),j); branch(brk(1,q1),brk(1,q2),k)
    return dict(status='PASS_PYTHON_PLAIN_BISIM_CHECK',branches=branches,
                halt_rows=halt_rows,max_non_test_segment_steps=max_segment)

def main():
    cert=read_cert(); p1=read_prog('Prog215.v'); p2=read_prog('DagPerm.v')
    packed=[(pack(a),pack(b),j,k) for a,b,z,j,k in cert]
    assert [(unpack(a),unpack(b),0,j,k) for a,b,j,k in packed]==cert
    forward=check(p1,p2,cert)
    backward=check(p2,p1,[(b,a,z,j,k) for a,b,z,j,k in cert])
    header='''(** Research prototype: kernel compilation NOT performed in this environment.
    The Python generator round-trips every path and branch index exactly. *)
From Coq Require Import List NArith.
From K230P Require Import Bisim230.
Import ListNotations.

Fixpoint decode_path (p : positive) : list bool :=
  match p with
  | xH => []
  | xO q => false :: decode_path q
  | xI q => true :: decode_path q
  end.

Definition packed_data : list (positive * positive * N * N) := [
'''
    data=';\n'.join('  (%d%%positive, %d%%positive, %d%%N, %d%%N)'%r for r in packed)
    footer='''
].
Definition Cert215Plain : list entry :=
  map (fun '(a,b,j,k) => (decode_path a,decode_path b,j,k)) packed_data.
'''
    packed_source=header+data+footer
    (HERE/'PackedCert215.v').write_text(packed_source)
    plain_source='''(** Research prototype, not compiled. Existing endpoint APIs need not change. *)
From Coq Require Import List.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm.
Require Import PackedCert215.
Import ListNotations.

Lemma certificate_forward_plain : check (ptree p215) (ptree dagPerm) Cert215Plain = true.
Proof. vm_compute. reflexivity. Qed.
Lemma certificate_backward_plain : check (ptree dagPerm) (ptree p215) (mirror Cert215Plain) = true.
Proof. vm_compute. reflexivity. Qed.
Theorem p215_dagPerm_plain R : rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof. exact (check_iff p215 dagPerm Cert215Plain certificate_forward_plain certificate_backward_plain R). Qed.
Print Assumptions p215_dagPerm_plain.
'''
    (HERE/'Source215Plain.v').write_text(plain_source)
    raw=read_pinned_source_bytes('Cert215Offsets.v')
    result=dict(status='PASS_DATA_ROUNDTRIP_AND_PYTHON_CHECKS_NOT_ROCQ',
        baseline_commit='b6fb232916d008383e7cf2990d68ddb30fded7db',
        certificate_sha256=hashlib.sha256(raw).hexdigest(),
        entries=len(cert),nonzero_offsets=sum(z!=0 for _,_,z,_,_ in cert),
        source_bytes_before=len(raw),source_bytes_after=len(packed_source.encode()),
        byte_reduction_percent=100*(1-len(packed_source.encode())/len(raw)),
        packed_sha256=hashlib.sha256(packed_source.encode()).hexdigest(),
        path_occurrences=2*len(cert),unique_paths=len({p for r in cert for p in r[:2]}),
        max_path_length=max(len(p) for r in cert for p in r[:2]),
        total_path_bits=sum(len(p) for r in cert for p in r[:2]),
        forward=forward,backward=backward,rocq_compiled=False,
        verification_scope='Exact lossless decoding and independent Python implementation of Bisim230.check; no kernel execution or complete endpoint rebuild.')
    (HERE/'prototype_result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
