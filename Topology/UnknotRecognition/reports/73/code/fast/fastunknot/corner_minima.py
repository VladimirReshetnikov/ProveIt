"""Deterministic dynamic minima for vertex-link triangle records.

This module is a data structure, not a topology checker.  The caller supplies
stable corner and vertex identities from independently verified local moves.
Every node caches thirteen least records, enough for a hypothetical deletion
of twelve corners.  Committed edits replenish the cache by AVL rotations.
"""
from dataclasses import dataclass


_PREFIX = 13


@dataclass(slots=True)
class _Node:
    key: tuple
    left: object = None
    right: object = None
    height: int = 1
    size: int = 1
    prefix: tuple = ()


def _height(node):
    return node.height if node is not None else 0


def _size(node):
    return node.size if node is not None else 0


class CornerMinimumIndex:
    """Maintain (global_vertex, stable_corner_id, nonnegative_value) records.

    Construction takes O(N log N) comparisons.  Inserting/deleting a record
    takes O(log(N+2)); hypothetical deletion of at most twelve records uses
    cached prefixes.  Larger simultaneous deletions use an ordered traversal.
    No search cost is proportional to the numeric normal-surface weight.
    """

    def __init__(self, records, link_euler, *, check=lambda: None):
        self.check = check
        self.link_euler = dict(link_euler)
        if any(type(v) is not int or type(e) is not int or e not in (1, 2)
               for v, e in self.link_euler.items()):
            raise ValueError('vertex ids are integers; link Euler values are 1 or 2')
        self.records = {}
        self.trees = {}
        self.stats = dict(comparisons=0, rotations=0, cache_updates=0,
                          ordered_visits=0, inserted=0, deleted=0)
        groups = {}
        for vertex, identity, value in records:
            self.check()
            self._validate_record(vertex, identity, value)
            if identity in self.records:
                raise ValueError('stable corner identities must be unique')
            self.records[identity] = (vertex, value)
            groups.setdefault(vertex, []).append((value, identity))
        if set(groups) != set(self.link_euler):
            raise ValueError('every vertex must have at least one corner record')
        for vertex, keys in groups.items():
            keys.sort()
            self.trees[vertex] = self._build(keys, 0, len(keys))

    def _validate_record(self, vertex, identity, value):
        if (type(vertex) is not int or vertex not in self.link_euler
                or type(identity) is not int or identity < 0
                or type(value) is not int or value < 0):
            raise ValueError('invalid vertex, stable corner identity, or triangle value')

    def _fix(self, node):
        self.check()
        self.stats['cache_updates'] += 1
        node.height = 1 + max(_height(node.left), _height(node.right))
        node.size = 1 + _size(node.left) + _size(node.right)
        left = node.left.prefix if node.left is not None else ()
        right = node.right.prefix if node.right is not None else ()
        node.prefix = (left + (node.key,) + right)[:_PREFIX]
        return node

    def _build(self, keys, low, high):
        if low == high:
            return None
        middle = (low + high) // 2
        return self._fix(_Node(keys[middle], self._build(keys, low, middle),
                              self._build(keys, middle + 1, high)))

    def _rotate_left(self, node):
        top = node.right
        node.right, top.left = top.left, node
        self._fix(node)
        self.stats['rotations'] += 1
        return self._fix(top)

    def _rotate_right(self, node):
        top = node.left
        node.left, top.right = top.right, node
        self._fix(node)
        self.stats['rotations'] += 1
        return self._fix(top)

    def _balance(self, node):
        self._fix(node)
        if _height(node.left) - _height(node.right) > 1:
            if _height(node.left.left) < _height(node.left.right):
                node.left = self._rotate_left(node.left)
            return self._rotate_right(node)
        if _height(node.right) - _height(node.left) > 1:
            if _height(node.right.right) < _height(node.right.left):
                node.right = self._rotate_right(node.right)
            return self._rotate_left(node)
        return node

    def _insert(self, node, key):
        self.check()
        if node is None:
            return self._fix(_Node(key))
        self.stats['comparisons'] += 1
        if key < node.key:
            node.left = self._insert(node.left, key)
        elif key > node.key:
            node.right = self._insert(node.right, key)
        else:
            raise ValueError('duplicate record key')
        return self._balance(node)

    def _delete(self, node, key):
        self.check()
        if node is None:
            raise ValueError('missing record key')
        self.stats['comparisons'] += 1
        if key < node.key:
            node.left = self._delete(node.left, key)
        elif key > node.key:
            node.right = self._delete(node.right, key)
        else:
            if node.left is None:
                return node.right
            if node.right is None:
                return node.left
            successor = node.right
            while successor.left is not None:
                self.check()
                successor = successor.left
            node.key = successor.key
            node.right = self._delete(node.right, successor.key)
        return self._balance(node)

    def minimum(self, vertex):
        tree = self.trees[vertex]
        return None if tree is None else tree.prefix[0][0]

    def count(self, vertex):
        return _size(self.trees[vertex])

    def prefix(self, vertex):
        tree = self.trees[vertex]
        return () if tree is None else tree.prefix

    def _surviving_minimum(self, vertex, removed):
        tree = self.trees[vertex]
        if tree is None:
            return None
        if len(removed) < _PREFIX:
            for value, identity in tree.prefix:
                self.check()
                if identity not in removed:
                    return value
            return None
        stack = []
        node = tree
        while node is not None or stack:
            while node is not None:
                self.check()
                stack.append(node)
                node = node.left
            node = stack.pop()
            self.stats['ordered_visits'] += 1
            if node.key[1] not in removed:
                return node.key[0]
            node = node.right
        return None

    def _edit(self, removals, additions):
        removed = list(removals)
        added = list(additions)
        if (any(type(i) is not int or i not in self.records for i in removed)
                or len(set(removed)) != len(removed)):
            raise ValueError('deleted stable corner identities must be distinct and live')
        ids = set()
        groups = {}
        for identity in removed:
            self.check()
            vertex, value = self.records[identity]
            groups.setdefault(vertex, [set(), []])[0].add(identity)
        for vertex, identity, value in added:
            self.check()
            self._validate_record(vertex, identity, value)
            if identity in self.records or identity in ids:
                raise ValueError('inserted stable corner identities must be fresh')
            ids.add(identity)
            groups.setdefault(vertex, [set(), []])[1].append(value)
        return removed, added, groups

    def score_edit(self, removals, additions):
        """Exact link contributions for a collective hypothetical local edit.

        Returns changes in the Euler characteristic and number of pieces of
        the removed vertex links.  Subtract them from the RAW surface changes.
        Simultaneous removals are processed collectively, not one at a time.
        """
        removed, added, groups = self._edit(removals, additions)
        vertices = []
        euler_delta = piece_delta = 0
        for vertex in sorted(groups):
            self.check()
            deleted, inserted = groups[vertex]
            old_min, old_count = self.minimum(vertex), self.count(vertex)
            survivor = self._surviving_minimum(vertex, deleted)
            possibilities = inserted + ([] if survivor is None else [survivor])
            new_count = old_count - len(deleted) + len(inserted)
            if new_count <= 0 or not possibilities:
                raise ValueError('the local edit must preserve every global vertex')
            new_min = min(possibilities)
            euler_delta += self.link_euler[vertex] * (new_min - old_min)
            piece_delta += new_min * new_count - old_min * old_count
            vertices.append(dict(vertex=vertex, minimum_before=old_min,
                minimum_after=new_min, corners_before=old_count,
                corners_after=new_count, link_euler=self.link_euler[vertex]))
        return dict(link_euler_delta=euler_delta, link_piece_delta=piece_delta,
                    vertices=vertices, deleted_records=len(removed),
                    inserted_records=len(added))

    def commit_edit(self, removals, additions):
        """Apply a valid local edit and refresh all cached prefixes.

        Callbacks must not interrupt a commit if the object will be reused;
        after an interruption, discard the index and rebuild from geometry.
        Validation errors are detected before any mutation.
        """
        removed, added, _ = self._edit(removals, additions)
        score = self.score_edit(removed, added)
        for identity in removed:
            vertex, value = self.records.pop(identity)
            self.trees[vertex] = self._delete(self.trees[vertex], (value, identity))
            self.stats['deleted'] += 1
        for vertex, identity, value in added:
            self.records[identity] = (vertex, value)
            self.trees[vertex] = self._insert(self.trees[vertex], (value, identity))
            self.stats['inserted'] += 1
        return score

    def verify_invariants(self):
        """Full structural audit for tests, independent of cached summaries."""
        found = {}

        def walk(node, vertex):
            if node is None:
                return [], 0
            left, lh = walk(node.left, vertex)
            right, rh = walk(node.right, vertex)
            keys = left + [node.key] + right
            assert keys == sorted(keys) and len(set(keys)) == len(keys)
            assert abs(lh-rh) <= 1 and node.height == 1+max(lh, rh)
            assert node.size == len(keys) and node.prefix == tuple(keys[:_PREFIX])
            value, identity = node.key
            assert identity not in found
            found[identity] = (vertex, value)
            return keys, node.height

        for vertex, tree in self.trees.items():
            keys, _ = walk(tree, vertex)
            assert keys
        assert found == self.records
        return True
