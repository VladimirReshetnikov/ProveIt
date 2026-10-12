"""Small homological interface models; these are NOT geometry certificates.

A Loop is a genuinely closed edge word. Surface circle orientations must be
provided in the convention specified in the article. No constructor here
certifies that the model is a 3-manifold, or that it embeds in S^3.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
import hashlib
import json
from typing import Any


def natural(value: int, name: str, minimum: int = 0) -> int:
    if type(value) is not int or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")
    return value


@dataclass(frozen=True)
class Loop:
    anchor: int
    word: tuple[int, ...] = ()  # signed, one-based edge numbers


@dataclass(frozen=True)
class Core:
    vertices: int
    edges: tuple[tuple[int, int], ...] = ()
    faces: tuple[Loop, ...] = ()
    three_cells: int = 0  # used only for the conditional Euler calculation


@dataclass(frozen=True)
class Surface:
    orientable: bool
    complexity: int  # genus when orientable; crosscaps otherwise
    boundary: int
    multiplicity: int = 1
    circles: tuple[Loop, ...] = ()
    intervals: tuple[int, ...] = ()  # core vertices: one per interval component

    @property
    def attached(self) -> bool:
        return bool(self.circles or self.intervals)

    @property
    def saturated(self) -> bool:
        return self.boundary > 0 and len(self.circles) == self.boundary

    @property
    def chi(self) -> int:
        return 2 - (2 if self.orientable else 1) * self.complexity - self.boundary


@dataclass(frozen=True)
class Model:
    core: Core
    surfaces: tuple[Surface, ...] = ()


def wire(value: Any) -> Any:
    """Unambiguous JSON-safe integers, including beyond CPython's decimal cap."""
    if type(value) is int:
        return {"$integer": ("-" if value < 0 else "") + hex(abs(value))[2:]}
    if isinstance(value, dict):
        return {str(k): wire(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [wire(x) for x in value]
    if value is None or type(value) in (bool, str):
        return value
    raise TypeError(f"unsupported wire type {type(value).__name__}")


def unwire(value: Any) -> Any:
    if isinstance(value, dict):
        if set(value) == {"$integer"}:
            text = value["$integer"]
            if type(text) is not str or not text or text in ("-", "+"):
                raise ValueError("invalid hexadecimal integer")
            sign, digits = (-1, text[1:]) if text.startswith("-") else (1, text)
            if not digits or any(c not in "0123456789abcdef" for c in digits):
                raise ValueError("noncanonical hexadecimal integer")
            if len(digits) > 1 and digits[0] == "0" or (sign < 0 and digits == "0"):
                raise ValueError("noncanonical hexadecimal integer")
            return sign * int(digits, 16)
        return {k: unwire(v) for k, v in value.items()}
    if isinstance(value, list):
        return [unwire(v) for v in value]
    return value


def fingerprint(model: Model) -> str:
    payload = json.dumps(wire(asdict(model)), sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode("ascii")).hexdigest()


def loop_chain(core: Core, loop: Loop) -> list[int]:
    if not isinstance(loop, Loop):
        raise ValueError("expected Loop")
    natural(loop.anchor, "loop anchor")
    if loop.anchor >= core.vertices:
        raise ValueError("loop anchor is outside core")
    chain = [0] * len(core.edges)
    vertex = loop.anchor
    for edge in loop.word:
        if type(edge) is not int or edge == 0 or abs(edge) > len(core.edges):
            raise ValueError("invalid signed edge")
        i = abs(edge) - 1
        a, b = core.edges[i]
        if edge < 0:
            a, b = b, a
        if vertex != a:
            raise ValueError("edge word is not contiguous")
        vertex = b
        chain[i] += 1 if edge > 0 else -1
    if vertex != loop.anchor:
        raise ValueError("edge word is not closed")
    return chain


def validate(model: Model) -> None:
    if not isinstance(model, Model) or not isinstance(model.core, Core):
        raise ValueError("expected Model with Core")
    core = model.core
    natural(core.vertices, "core vertices")
    natural(core.three_cells, "core three_cells")
    if core.vertices == 0 and (core.edges or core.faces or core.three_cells):
        raise ValueError("empty core cannot have positive-dimensional cells")
    for edge in core.edges:
        if len(edge) != 2:
            raise ValueError("edge must have two endpoints")
        for v in edge:
            natural(v, "edge endpoint")
            if v >= core.vertices:
                raise ValueError("edge endpoint outside core")
    for face in core.faces:
        loop_chain(core, face)
    for s in model.surfaces:
        if not isinstance(s, Surface) or type(s.orientable) is not bool:
            raise ValueError("surface orientable must be bool")
        natural(s.complexity, "surface complexity", 0 if s.orientable else 1)
        natural(s.boundary, "surface boundary")
        natural(s.multiplicity, "surface multiplicity", 1)
        if len(s.circles) > s.boundary:
            raise ValueError("too many attached boundary circles")
        if s.saturated and s.intervals:
            raise ValueError("a saturated boundary has no remaining intervals")
        if s.attached and s.multiplicity != 1:
            raise ValueError("a ported surface must have multiplicity one")
        if s.boundary == 0 and s.attached:
            raise ValueError("a closed surface has no boundary ports")
        for c in s.circles:
            loop_chain(core, c)
        for v in s.intervals:
            natural(v, "interval anchor")
            if v >= core.vertices:
                raise ValueError("interval anchor outside core")
