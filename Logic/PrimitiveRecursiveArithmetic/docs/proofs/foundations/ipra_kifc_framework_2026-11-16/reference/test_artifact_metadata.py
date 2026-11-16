from __future__ import annotations

import json
import unittest
from pathlib import Path

import jsonschema

from reference.kifc_reference import FiniteRelationTower


ROOT = Path(__file__).resolve().parents[1]


class GraphSchemaTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.schema = json.loads((ROOT / "metadata/framework_schema.json").read_text())

    def test_graph_examples_validate(self) -> None:
        for name in ("cubic_bisection_graph.json", "relational_bisection_graph.json"):
            with self.subTest(name=name):
                data = json.loads((ROOT / "examples" / name).read_text())
                jsonschema.Draft202012Validator(self.schema).validate(data)

    def test_graph_dependencies_are_topological(self) -> None:
        for path in sorted((ROOT / "examples").glob("*_graph.json")):
            data = json.loads(path.read_text())
            position = {node["id"]: i for i, node in enumerate(data["nodes"])}
            self.assertIn(data["terminal"], position)
            for node in data["nodes"]:
                for dependency in node["dependencies"]:
                    self.assertIn(dependency, position)
                    self.assertLess(position[dependency], position[node["id"]])


class RelationFixtureTests(unittest.TestCase):
    def test_dead_end_fixture(self) -> None:
        data = json.loads((ROOT / "examples/dead_end_relation.json").read_text())
        edge_set = {tuple(edge) for edge in data["edges"]}
        tower = FiniteRelationTower(
            tuple(tuple(level) for level in data["levels"]),
            edge=lambda level, a, b: (level, a, b) in edge_set,
        )
        horizon = len(data["levels"]) - 1
        viable = [sorted(row) for row in tower.viable_sets(horizon)]
        self.assertEqual(viable, data["expected_viable"])
        self.assertEqual(
            list(tower.least_viable_path(horizon)),
            data["expected_least_path"],
        )


if __name__ == "__main__":
    unittest.main()
