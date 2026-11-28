import os
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import Mock

from lean_dep_cache import compile_cached, key, store_cached


class LeanDependencyCacheTests(unittest.TestCase):
    def test_keys_follow_transitive_source_changes(self):
        base = "PEqualNP.Outside.L_base"
        middle = "PEqualNP.Outside.L_middle"
        root = "PEqualNP.Outside.L_root"
        state = b"frozen-toolchain-and-mathlib"

        def root_key(source):
            keys = {base: key(state, base, source, {})}
            keys[middle] = key(state, middle, f"import {base}\r\n".encode(), keys)
            return key(state, root, f"import {middle}\n".encode(), keys)

        self.assertNotEqual(root_key(b"original"), root_key(b"changed"))
        self.assertNotEqual(key(state, base, b"source", {}), key(b"new-toolchain", base, b"source", {}))

    @unittest.skipUnless(os.name == "posix", "the Jenkins cache uses Linux file locks")
    def test_second_job_reuses_only_the_complete_dependency_artifact(self):
        with TemporaryDirectory() as temporary:
            store = Path(temporary)
            first = store / "cold.olean"
            second = store / "warm.olean"
            compile_cached(store, "PEqualNP.Outside.L_test", "a" * 64, first,
                           lambda: first.write_bytes(b"compiled in the sandbox"))
            compile_again = Mock()
            compile_cached(store, "PEqualNP.Outside.L_test", "a" * 64, second, compile_again)
            compile_again.assert_not_called()
            self.assertEqual(first.read_bytes(), second.read_bytes())

    @unittest.skipUnless(os.name == "posix", "the Jenkins cache uses Linux file locks")
    def test_accepted_leaf_artifact_warms_downstream_dependency_lookup(self):
        with TemporaryDirectory() as temporary:
            store = Path(temporary)
            leaf = store / "leaf.olean"
            downstream = store / "downstream.olean"
            leaf.write_bytes(b"accepted submission olean")
            digest = key(b"ctx", "Conjectures.Goldbach.Leaf", b"import Mathlib\n", {})
            self.assertTrue(store_cached(store, "Conjectures.Goldbach.Leaf", digest, leaf))
            self.assertFalse(store_cached(store, "Conjectures.Goldbach.Leaf", digest, leaf))
            build = Mock()
            compile_cached(store, "Conjectures.Goldbach.Leaf", digest, downstream, build)
            build.assert_not_called()
            self.assertEqual(downstream.read_bytes(), b"accepted submission olean")
