#!/usr/bin/env python3
"""Render a compact, kernel-checked replay of Source 149's rho8 certificate.

The Python optimizer is untrusted. It replaces exact substitution instances of
previous theorem schemas, retains the root dependency closure, and emits a finite
program for the sound Rocq interpreter. Only the kernel-checked final result is
used by rho8_all. No Python assertion is a premise of the exported theorem.

The earlier-schema reuse optimization was developed with the parallel Lean
reflection implementation. Both start from the same delivered certificate.
"""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def render(certificate, generic_path, output, metadata=None):
    data = json.loads(certificate.read_text())
    assert data['format'] == 'term_dag_v1'
    terms, index = [], {}

    def put(term):
        if term not in index:
            index[term] = len(terms)
            terms.append(term)
        return index[term]

    for i, term in enumerate(data['term_table']):
        key = (('z',) if term == 'T' else ('v', term['var'])
               if isinstance(term, dict) else ('i', *term))
        assert put(key) == i
    zero = index[('z',)]

    def imp(x, y):
        return zero if x == y == zero else put(('i', x, y))

    def substitute(x, env, cache=None):
        if cache is None:
            cache = {}
        if x not in cache:
            term = terms[x]
            if term[0] == 'z':
                cache[x] = zero
            elif term[0] == 'v':
                cache[x] = env.get(term[1], zero)
            else:
                cache[x] = imp(substitute(term[1], env, cache),
                               substitute(term[2], env, cache))
        return cache[x]

    def renaming(x, y, rho):
        tx, ty = terms[x], terms[y]
        if tx[0] == 'v':
            assert ty[0] == 'v' and rho.setdefault(tx[1], ty[1]) == ty[1]
        elif tx[0] == 'z':
            assert ty == tx
        else:
            assert ty[0] == 'i'
            renaming(tx[1], ty[1], rho)
            renaming(tx[2], ty[2], rho)

    def parts(i):
        term = terms[i]
        assert term[0] == 'i'
        return term[1:]

    def rho_args(term):
        left, right = parts(term)
        cu, a = parts(left)
        c, u = parts(cu)
        ac, bc = parts(right)
        a2, c2 = parts(ac)
        b, c3 = parts(bc)
        assert a2 == a and c2 == c3 == c
        return [a, b, c, u]

    def env_list(env):
        return [env.get(i, zero) for i in range(max(env, default=-1) + 1)]

    # A strict syntactic match suffices. Normalization is not needed here.
    sizes = []
    for term in data['term_table']:
        sizes.append(1 + sizes[term[0]] + sizes[term[1]]
                     if isinstance(term, list) else 1)

    def match_schema(pattern, target, env, seen):
        if (pattern, target) in seen:
            return True
        seen.add((pattern, target))
        pt, tt = terms[pattern], terms[target]
        if pt[0] == 'v':
            return env.setdefault(pt[1], target) == target
        if pt[0] == 'z':
            return tt[0] == 'z'
        return (tt[0] == 'i'
                and match_schema(pt[1], tt[1], env, seen)
                and match_schema(pt[2], tt[2], env, seen))

    patterns, replacements = [], {}
    for node in data['nodes']:
        for previous in patterns:
            old = data['nodes'][previous]
            if sizes[old['term']] > sizes[node['term']]:
                continue
            env = {}
            if match_schema(old['term'], node['term'], env, set()):
                replacements[node['id']] = {
                    'kind': 'substitution', 'parent': previous,
                    'substitution': env}
                break
        else:
            patterns.append(node['id'])

    needed_nodes = set()

    def need_node(i):
        if i in needed_nodes:
            return
        needed_nodes.add(i)
        rule = replacements.get(i, data['nodes'][i]['rule'])
        for field in ('major', 'minor', 'parent'):
            if field in rule:
                assert rule[field] < i
                need_node(rule[field])

    need_node(len(data['nodes']) - 1)
    steps, oldmap = [], {}

    def emit(term, rule):
        steps.append((term, rule))
        return len(steps) - 1

    for node in data['nodes']:
        if node['id'] not in needed_nodes:
            continue
        term = node['term']
        rule = replacements.get(node['id'], node['rule'])
        kind = rule['kind']
        if kind == 'truth':
            new = emit(term, ('truth',))
        elif kind == 'dominated_rho8':
            new = emit(term, ('ax', *rho_args(term)))
        elif kind == 'mp':
            new = emit(term, ('mp', oldmap[rule['major']], oldmap[rule['minor']]))
        elif kind == 'substitution':
            env = {int(k): v for k, v in rule['substitution'].items()}
            assert substitute(data['nodes'][rule['parent']]['term'], env) == term
            new = emit(term, ('inst', oldmap[rule['parent']], env_list(env)))
        elif kind == 'mp_substitution':
            me = {int(k): v for k, v in rule['major_substitution'].items()}
            ne = {int(k): v for k, v in rule['minor_substitution'].items()}
            major = substitute(data['nodes'][rule['major']]['term'], me)
            _, consequent = parts(major)
            rho = {}
            renaming(consequent, term, rho)
            ren = {i: index[('v', j)] for i, j in rho.items()}
            # Standardize both premises with the same valuation; omitted
            # variables denote truth, just as in the source certificate.
            me = {i: substitute(x, ren) for i, x in me.items()}
            ne = {i: substitute(x, ren) for i, x in ne.items()}
            major = substitute(data['nodes'][rule['major']]['term'], me)
            minor = substitute(data['nodes'][rule['minor']]['term'], ne)
            assert parts(major) == (minor, term)
            m = emit(major, ('inst', oldmap[rule['major']], env_list(me)))
            n = emit(minor, ('inst', oldmap[rule['minor']], env_list(ne)))
            new = emit(term, ('mp', m, n))
        else:
            raise ValueError(kind)
        oldmap[node['id']] = new

    # MP and substitution conclusions are computed by the interpreter, so
    # only axiom parameters and substitution environments need term data.
    needed_terms = set()

    def need_term(i):
        if i in needed_terms:
            return
        needed_terms.add(i)
        if terms[i][0] == 'i':
            need_term(terms[i][1])
            need_term(terms[i][2])

    for _, rule in steps:
        references = rule[1:] if rule[0] == 'ax' else rule[2] if rule[0] == 'inst' else []
        for i in references:
            need_term(i)
    selected = sorted(needed_terms)
    positions = {old: i for i, old in enumerate(selected)}
    count = len(selected)

    def ref(i):
        return count - 1 - positions[i]

    generic = generic_path.read_text()
    marker = 'End Certificate.\nPrint Assumptions Certificate.check_sound.'
    assert generic.count(marker) == 1
    certificate_sha = hashlib.sha256(certificate.read_bytes()).hexdigest()
    lines = [f'''(** Compact replay of Source 149's dominated-rho8 certificate.
    Certificate SHA256: {certificate_sha}.
    Retained original nodes: {len(needed_nodes)}; instructions: {len(steps)};
    symbolic DAG entries: {count}. The generator is untrusted. *)
''', generic.replace(marker, ''), '''
Definition ti (a b : N) := TImp (N.to_nat a) (N.to_nat b).
Definition ax (a b c u : N) := Ax (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat u).
Definition mp (major minor : N) := MP (N.to_nat major) (N.to_nat minor).
Definition inst (parent : N) (env : list N) := Inst (N.to_nat parent) (map N.to_nat env).

Definition term_data : list term := [''']
    for i, old in enumerate(selected):
        term = terms[old]
        if term[0] == 'z':
            line = 'TZero'
        elif term[0] == 'v':
            line = f'TVar {term[1]}'
        else:
            line = f'ti {i - 1 - positions[term[1]]} {i - 1 - positions[term[2]]}'
        lines.append(line + (';' if i < count - 1 else '].'))
    lines.append('Definition proof_data : list rule := [')
    for i, (_, rule) in enumerate(steps):
        if rule[0] == 'truth':
            line = 'Truth'
        elif rule[0] == 'ax':
            line = 'ax ' + ' '.join(str(ref(x)) for x in rule[1:])
        elif rule[0] == 'mp':
            line = f'mp {i - 1 - rule[1]} {i - 1 - rule[2]}'
        else:
            line = f'inst {i - 1 - rule[1]} [' + '; '.join(str(ref(x)) for x in rule[2]) + ']%N'
        lines.append(line + (';' if i < len(steps) - 1 else '].'))
    lines.append('''Definition target := rho (V 0) (V 1) (V 2) (V 3).
Lemma certificate_checked : check (decode term_data) proof_data target = true.
Proof. vm_compute. reflexivity. Qed.
End Certificate.
Print Assumptions Certificate.check_sound.

(** Every rho8 instance follows from the dominated instances. *)
Theorem rho8_all (T : nat -> Prop) (h : DomImp T) a b c u : T (rho8 a b c u).
Proof.
 pose proof (Certificate.check_sound T h (Certificate.decode Certificate.term_data)
   Certificate.proof_data Certificate.target Certificate.certificate_checked) as H.
 specialize (H (fun i => nth i [a;b;c;u] 0)).
 unfold Certificate.target in H. rewrite Certificate.eval_rho in H. exact H.
Qed.
Print Assumptions rho8_all.
''')
    output.write_text('\n'.join(lines), encoding='utf-8', newline='\n')
    result = {
        'certificate_sha256': certificate_sha,
        'retained_original_nodes': len(needed_nodes),
        'schema_replacements': len(replacements), 'term_count': count,
        'steps': len(steps),
        'generic_sha256': hashlib.sha256(generic_path.read_bytes()).hexdigest(),
        'source_sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
        'source_bytes': output.stat().st_size}
    if metadata is not None:
        metadata.write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path,
                        default=ROOT / 'lean217/dominated_rho8_full_certificate.json')
    parser.add_argument('--generic', type=Path,
                        default=ROOT / 'rocqdom/DomRho8Reflection.v')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--metadata', type=Path)
    args = parser.parse_args()
    print(json.dumps(render(args.certificate, args.generic, args.output, args.metadata)))


if __name__ == '__main__':
    main()
