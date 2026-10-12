"""Exact best-value dictionaries: deterministic AVL and optional Python hash tables.

Values are (score, prefix_position); higher score and then earlier position win.
The AVL backend supplies the deterministic complexity bound in the article.
"""
from __future__ import annotations
from dataclasses import dataclass

Key = tuple[int, int]
Value = tuple[int, int]


def better(new: Value, old: Value) -> bool:
    return new[0] > old[0] or (new[0] == old[0] and new[1] < old[1])


@dataclass(slots=True)
class _Node:
    key: Key
    value: Value
    left: _Node | None = None
    right: _Node | None = None
    height: int = 1


def _height(node: _Node | None) -> int:
    return 0 if node is None else node.height


def _fix(node: _Node) -> None:
    node.height = 1 + max(_height(node.left), _height(node.right))


def _right(node: _Node) -> _Node:
    top = node.left
    assert top is not None
    node.left = top.right
    top.right = node
    _fix(node)
    _fix(top)
    return top


def _left(node: _Node) -> _Node:
    top = node.right
    assert top is not None
    node.right = top.left
    top.left = node
    _fix(node)
    _fix(top)
    return top


class AVLBestMap:
    __slots__ = ('root', 'size')

    def __init__(self) -> None:
        self.root: _Node | None = None
        self.size = 0

    def get(self, key: Key) -> Value | None:
        node = self.root
        while node is not None:
            if key == node.key:
                return node.value
            node = node.left if key < node.key else node.right
        return None

    def put_best(self, key: Key, value: Value) -> None:
        def insert(node: _Node | None) -> _Node:
            if node is None:
                self.size += 1
                return _Node(key, value)
            if key == node.key:
                if better(value, node.value):
                    node.value = value
                return node
            if key < node.key:
                node.left = insert(node.left)
            else:
                node.right = insert(node.right)
            _fix(node)
            balance = _height(node.left) - _height(node.right)
            if balance > 1:
                assert node.left is not None
                if key > node.left.key:
                    node.left = _left(node.left)
                return _right(node)
            if balance < -1:
                assert node.right is not None
                if key < node.right.key:
                    node.right = _right(node.right)
                return _left(node)
            return node
        self.root = insert(self.root)


class HashBestMap:
    __slots__ = ('table',)

    def __init__(self) -> None:
        self.table: dict[Key, Value] = {}

    @property
    def size(self) -> int:
        return len(self.table)

    def get(self, key: Key) -> Value | None:
        return self.table.get(key)

    def put_best(self, key: Key, value: Value) -> None:
        old = self.table.get(key)
        if old is None or better(value, old):
            self.table[key] = value
