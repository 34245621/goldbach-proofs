import unittest

from event_routes import route, unsupported_lean_path


class EventRoutesTest(unittest.TestCase):
    def test_registered_conjecture_proof_routes_to_advisory(self):
        self.assertFalse(unsupported_lean_path("lean/Conjectures/Goldbach/Example.lean"))
        self.assertEqual(
            route("pull_request", {"action": "opened"},
                  ["lean/Conjectures/Goldbach/Example.lean"]),
            ["advisory"],
        )

    def test_legacy_lean_file_routes_to_explicit_advisory_refusal(self):
        self.assertTrue(unsupported_lean_path("lean/legacy/Example.lean"))
        self.assertEqual(
            route("pull_request", {"action": "opened"},
                  ["lean/legacy/Example.lean"]),
            ["advisory"],
        )

    def test_supported_base_sources_keep_their_special_routes(self):
        self.assertFalse(unsupported_lean_path("lean/ResearchSupport/Defs.lean"))
        self.assertEqual(
            route("pull_request", {"action": "opened"},
                  ["lean/ResearchSupport/Defs.lean"]),
            [],
        )
        self.assertEqual(
            route("pull_request", {"action": "opened"},
                  ["lean/ResearchSupport/GRH.lean"]),
            ["grh"],
        )


if __name__ == "__main__":
    unittest.main()
