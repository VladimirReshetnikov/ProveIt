from __future__ import annotations
import re, time, json, sys, random
from z3local import Solver

def OR(a):
    a=list(a)
    if not a:return 'false'
    if len(a)==1:return a[0]
    return '(or '+' '.join(a)+')'
def AND(a):
    a=list(a)
    if not a:return 'true'
    if len(a)==1:return a[0]
    return '(and '+' '.join(a)+')'
def columns(fam, m=6): return [j for j in range(1 << m) if fam>>j&1]
def search(m, fam, timeout=5000, permutation=True):
    cols=columns(fam,m);n=len(cols);k=sum(c.bit_count() for c in cols)
    fw=max(1,(m-1).bit_length())
    ps=[f'p{i}_{j}' for i in range(m) for j in range(n)]
    width=max(1,(n-1).bit_length())
    bv=lambda x,w:f'(_ bv{x} {w})'
    lines=['(set-option :produce-models true)',f'(set-option :timeout {timeout})']
    for i in range(m):
        lines += [f'(declare-const f{i} (_ BitVec {fw}))'
                  ]
        if m!=(1<<fw):lines +=[f'(assert (bvult f{i} {bv(m,fw)}))']
    if permutation:lines += ['(assert (distinct '+' '.join(f'f{i}' for i in range(m))+'))']
    for j in range(n):
        lines += [f'(declare-const g{j} (_ BitVec {width}))']
        if n!=(1<<width):lines +=[f'(assert (bvult g{j} {bv(n,width)}))']
    for p in ps:lines +=[f'(declare-const {p} Bool)']
    for i in range(m):
        lines += ['(assert '+OR(f'p{i}_{j}' for j in range(n))+')']
    for j in range(n):
        lines += ['(assert '+OR(f'p{i}_{j}' for i in range(m))+')']
    lines += ['(assert ((_ at-most '+str(k-1)+') '+' '.join(ps)+'))']
    for i in range(m):
        for j in range(n):
            legal_f=OR(f'(= f{i} {bv(r,fw)})' for r in range(m) if cols[j]>>r&1)
            legal_g=OR(f'(= g{j} {bv(c,width)})' for c in range(n) if cols[c]>>i&1)
            lines += [f'(assert (=> p{i}_{j} (and {legal_f} {legal_g})))']
    for r in range(m):
        for c in range(n):
            if cols[c]>>r&1:
                coverage=[f'(and p{i}_{c} (= f{i} {bv(r,fw)}))' for i in range(m)]
                coverage +=[f'(and p{r}_{j} (= g{j} {bv(c,width)}))' for j in range(n)]
                lines +=['(assert '+OR(coverage)+')']
    with Solver() as s:
        out=s.evaluate('\n'.join(lines)+'\n(check-sat)')
        if out.strip()!='sat':return {'status':out.strip(),'m':m,'family':fam}
        values=s.evaluate('(get-value ('+' '.join([f'f{i}' for i in range(m)]+[f'g{j}' for j in range(n)]+ps)+'))')
    pairs=dict(re.findall(r'\((\w+)\s+(true|false|#[bx][0-9a-f]+)\)',values))
    def v(key):
        st=pairs[key]
        if st.startswith('#b'):return int(st[2:],2)
        if st.startswith('#x'):return int(st[2:],16)
        return st=='true'
    f=[v(f'f{i}') for i in range(m)];g=[v(f'g{j}') for j in range(n)]
    T=[(i,j) for i in range(m) for j in range(n) if v(f'p{i}_{j}')]
    S={(i,j) for i in range(m) for j in range(n) if cols[j]>>i&1}
    img={(f[i],j) for i,j in T}|{(i,g[j]) for i,j in T}
    assert img==S and len(T)<len(S)
    assert len({i for i,j in T})==m and len({j for i,j in T})==n
    return {'status':'sat','m':m,'family':fam,'columns':cols,'f':f,'g':g,'T':T}


def main():
    import argparse
    from pathlib import Path
    parser = argparse.ArgumentParser(description='Optional SMT predecessor discovery; verification does not need this tool.')
    parser.add_argument('--rows', type=int, required=True)
    parser.add_argument('--family', type=int, required=True)
    parser.add_argument('--timeout-ms', type=int, default=10000)
    parser.add_argument('--allow-nonpermutation', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if not 2 <= args.rows <= 6 or not 0 < args.family < (1 << (1 << args.rows)):
        parser.error('Rows must be 2 through 6 and family must be a nonempty in-range bit mask')
    if args.timeout_ms < 1:
        parser.error('Timeout must be positive')
    result = search(args.rows, args.family, args.timeout_ms, not args.allow_nonpermutation)
    text = json.dumps(result, indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
    if result['status'] != 'sat':
        raise SystemExit(2)


if __name__ == '__main__':
    main()
