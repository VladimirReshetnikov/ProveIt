"""Python model of K230's Dag230.v (structured source) and RM.v/Bisim230.v tree expansion.

  parse(path)            -> dict n -> (edge, edge), edges as ('N', n) or (op, arg)
  expand(nodes, e, atoms) -> the atom word of an edge (ProgLib230.expand with unbounded fuel)
  sites(nodes, root, nn) -> leaf list of ptree (to_tree p (nnodes+1) root): [bits, op, arg]
"""
import re, sys

sys.setrecursionlimit(100000)
EDGE = re.compile(r"(ENode|EInc|EDecnz|EBreak|EContinue|EHalt)\s*(\d*)")


def edge(txt):
    m = EDGE.fullmatch(txt.strip())
    op, a = m.group(1), m.group(2)
    if op == "ENode":
        return ("N", int(a))
    return (op, int(a) if a else None)


def parse(path):
    nodes = {}
    for line in open(path, encoding="utf-8"):
        m = re.match(r"\s*\|\s*(\d+)\s*=>\s*\((.*),(.*)\)\s*$", line)
        if m:
            nodes[int(m.group(1))] = (edge(m.group(2)), edge(m.group(3)))
    return nodes


def atoms_of(path):
    s = open(path, encoding="utf-8").read()
    m = re.search(r"Definition atoms : list nat := \[([^\]]*)\]", s)
    return [int(x) for x in m.group(1).split(";")]


def expand(nodes, e, atoms):
    if e[0] != "N" or e[1] in atoms:
        return [e]
    a, b = nodes.get(e[1], (("EHalt", None), ("EHalt", None)))
    return expand(nodes, a, atoms) + expand(nodes, b, atoms)


def sites(nodes, root, nn):
    out = []

    def go(n, fuel, path):
        if fuel == 0:
            return  # TX: walk fails
        a, b = nodes.get(n, (("EHalt", None), ("EHalt", None)))
        for bit, e in (("0", a), ("1", b)):
            if e[0] == "N":
                if fuel - 1 == 0:
                    continue
                go(e[1], fuel - 1, path + bit)
            else:
                out.append([path + bit, e[0], e[1]])

    go(root, nn + 1, "")
    return out
