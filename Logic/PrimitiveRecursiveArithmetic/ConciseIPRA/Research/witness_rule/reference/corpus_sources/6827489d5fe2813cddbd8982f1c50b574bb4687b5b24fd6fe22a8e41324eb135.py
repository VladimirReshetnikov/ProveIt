"""Untrusted proof-format compiler; imported by no kernel.

Reconstructs a successful canonical two-field Choice-DI checking trace,
then emits four-field packets with an allocation at every continuation.
For the byte profile, first use reference/compile_focused.py to expand
object assumptions into elimination-only uses. Both inherited adapters
are attributed in reference/PROVENANCE.txt.
"""
import copy
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'reference'))
from translate_uniform_original import Node, Trace as OldTrace, Compiler as OldCompiler
from compile_focused import compile_packet


class Trace(OldTrace):
    def __init__(self, packet, focused=False):
        super().__init__(packet)
        self.focused = focused
        if focused:
            self.goal = self.opening(self.goal)

    def check(self, a, g):
        if not self.focused and self.opening(a) in g:
            return Node('hyp', a)
        packet = self.data.pop()
        m, t = packet
        node = Node('', a, packet)
        if m:
            if self.focused and self.opening(m) in g:
                node.children.append(Node('hyp', m))
            else:
                node.children.append(self.check(m, g))
            h = m[2:]
            if not h:
                node.kind = 'specialize'
                s, u, t = m + [t] if m[1:] else [0, t] + m
                if self.opening(t, u) != a:
                    raise ValueError('Source specialization does not match')
                node.children.append(self.check(self.opening(t, s), g))
                return node
            node.kind = 'eliminate'
        elif t:
            node.kind = 'introduce'
            h = a = self.opening(a[2], t, 2)
        else:
            node.kind = 'compute'
            (n, initial, update), result = a
            initial = self.opening(self.opening(update, *n, 3), [*n, initial, update], 1) if n else [initial]
            if result != initial:
                raise ValueError('Source computation does not match')
            return node
        self.k -= 1
        node.allocated = self.k
        image = self.k if m or len(a) % 2 == m else 0
        node.children.append(self.check(self.opening(a, [self.k]),
                                       g + [self.opening(h, image)]))
        return node


class Compiler(OldCompiler):
    def __init__(self, focused=False):
        super().__init__()
        self.focused = focused

    def compile(self, node, a, g):
        if not self.focused and self.opening(a) in g:
            self.forget(node)
            return
        if node.kind == 'hyp':
            raise ValueError('Unexpanded hypothesis reached a focused minor')
        old_m, old_t = node.packet
        packet = [self.rename(old_m), 0, 0, None]
        self.consumed.append(packet)
        m = packet[0]
        if old_m:
            if self.focused and self.opening(m) in g:
                self.forget(node.children[0])
            else:
                self.compile(node.children[0], m, g)
        t = self.rename(old_t)
        if type(m) is list and len(m) == 1:
            packet[1:] = [0, t, m[0]]
        elif type(m) is list and len(m) == 2:
            packet[1:] = [m[0], m[1], t]
        else:
            packet[3] = t

        if node.kind == 'compute':
            (n, initial, update), result = a
            initial = self.opening(self.opening(update, *n, 3), [*n, initial, update], 1) if n else [initial]
            if result != initial:
                raise ValueError('Translated computation does not match')
            return
        if node.kind == 'specialize':
            _, source, target, template = packet
            if self.opening(template, target) != a:
                raise ValueError('Translated specialization does not match')
            a = self.opening(template, source)
            h = []
            self.administrative_allocations += 1
        elif node.kind == 'eliminate':
            h = m[2:]
        elif node.kind == 'introduce':
            h = a = self.opening(a[2], t, 2)
        else:
            raise ValueError('Unknown trace kind')
        self.k -= 1
        if node.allocated is not None:
            self.names[node.allocated] = self.k
        image = self.k if m or len(a) % 2 == m else 0
        self.compile(node.children[-1], self.opening(a, [self.k]),
                     g + [self.opening(h, image)])

    def add_unmatched_prefix(self, kind):
        """A valid major, followed by a deliberately mismatched instruction."""
        major = [[[0], 0, 3], 0]
        if kind == 'endpoints':
            packet = [major, 0, 0, 0]
        elif kind == 'target':
            # Actual endpoints, but the constant false motive cannot match
            # any inherited positive test goal used by this test producer.
            packet = [major, major[0], 0, [0, [0]]]
        else:
            raise ValueError(kind)
        self.consumed.extend([packet, [0, 0, 0, 0]])
        self.k -= 1
        self.administrative_allocations += 1
        return [[]]


def translate(packet, focused=False, unmatched=None):
    focused_stats = None
    if focused:
        packet, focused_stats = compile_packet(packet)
    trace = Trace(packet, focused)
    tree = trace.run()
    compiler = Compiler(focused)
    context = compiler.add_unmatched_prefix(unmatched) if unmatched else []
    compiler.compile(tree, trace.goal, context)
    result = list(reversed(compiler.consumed)) + [trace.goal]
    return result, {
        'focused': focused,
        'old_allocations': -trace.k,
        'new_allocations': -compiler.k,
        'administrative_allocations': compiler.administrative_allocations,
        'pruned_trace_nodes': compiler.pruned_nodes,
        'unmatched_prefix': unmatched,
        'focused_translation': focused_stats,
    }
