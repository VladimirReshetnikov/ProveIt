"""Generate the mechanical regions of coq/ProgLib254.v from coq/Dag254.v (rewrites the GENERATED
regions in place): the while_decnz loops with increment-only bodies, their dispatch tactic, and the
atom list.  Usage: python -I tools/gen_prog.py"""
import re
from pathlib import Path
COQ = Path(__file__).resolve().parent.parent / 'coq'
txt = (COQ / 'Dag254.v').read_text(encoding='utf-8')
nodes, names = {}, {}
for m in re.finditer(r'\| (\d+) => \((.*?), (E\w+(?: \d+)?)\)\s+\(\* (.*?) \*\)', txt):
    nodes[int(m.group(1))] = (m.group(2), m.group(3)); names[int(m.group(1))] = m.group(4)
byname = {v: k for k, v in names.items()}


def num(e, kind):
    m = re.fullmatch(kind + r' (\d+)', e)
    return int(m.group(1)) if m else None


def inc_tree(e):
    """targets of an edge that is a tree of increments (left to right), else None"""
    if num(e, 'EInc') is not None:
        return [num(e, 'EInc')]
    n = num(e, 'ENode')
    if n is None:
        return None
    a, b = inc_tree(nodes[n][0]), inc_tree(nodes[n][1])
    return None if a is None or b is None else a + b


def loop_info(n):
    car, cdr = nodes[n]
    r = num(car, 'EDecnz')
    if r is None:
        return None
    if cdr == 'EContinue 1':
        return r, []
    b = num(cdr, 'ENode')
    if b is None or nodes[b][1] != 'EContinue 2':
        return None
    t = inc_tree(nodes[b][0])
    if t is None or r in t:
        return None
    return r, t


LOOPS = {n: loop_info(n) for n in sorted(nodes) if loop_info(n) is not None}


def wrap(s):
    return s if s == 'm' else f'({s})'


def loops():
    out = []
    for n, (r, ts) in LOOPS.items():
        post = 'm'
        for t in sorted(set(ts)):
            k = ts.count(t)
            post = f'set {wrap(post)} {t} (get m {t} + {"" if k == 1 else f"{k} * "}get m {r})'
        post = f'set {wrap(post)} {r} 0'
        g = 'm'
        for t in ts:
            g = f'inc {t} {wrap(g)}'
        out.append(f'(* {names[n]} *)\nLemma w{n} m : sem (ENode {n}) m XNormal ({post}).\n'
                   f'Proof. revert m; while_tac (fun m : St => {g}) (fun m : St => {post}). Qed.')
    body = '\n'.join(out) + '\n'
    body += 'Ltac elem_w := match goal with\n'
    body += ''.join(f'  | |- sem (ENode {n}) _ _ _ => apply w{n}\n' for n in LOOPS) + '  end.'
    return body


# nodes with their own lemma (loops, helpers with control flow, subroutines used as stack ops)
ATOM_NAMES = ['fn_14().0', 'fn_41().0', 'pair(scratch2,scratch1,topwff).0', 'if_eq().n_055.0',
              'if_eq(scratch1,param2,40).0', 'if_eq(scratch1,param2,77).0', 'if_eq(scratch1,param2,halt).0',
              'if_not_decnz(prooflist,5).0', 'pushwff().0', 'v_1().0', 'par1().0', 'fn_59().0', 'par3().0',
              'fn_45().0', 'wel().0', 'wal().0', 'weq().0', 'wn().0', 'wex().0', 'wa().0', 'node_108.0',
              'node_110.0', 'read(axiomcode).0', 'read(param1).0', 'read(param2).0', 'pop(param2).0',
              'main().3']


def atoms():
    A = sorted(set(LOOPS) | {byname[x] for x in ATOM_NAMES})
    return 'Definition atoms : list nat := [' + '; '.join(map(str, A)) + '].'


def replace_region(src, tag, body):
    a = f'(* BEGIN GENERATED {tag} *)\n'
    b = f'(* END GENERATED {tag} *)'
    i = src.index(a) + len(a)
    j = src.index(b)
    return src[:i] + body + '\n' + src[j:]


if __name__ == '__main__':
    p = COQ / 'ProgLib254.v'
    src = p.read_text(encoding='utf-8')
    src = replace_region(src, 'loops', loops())
    src = replace_region(src, 'atoms', atoms())
    p.write_text(src, encoding='utf-8', newline='\n')
    print('loops', len(LOOPS), {names[n]: v for n, v in LOOPS.items()})
