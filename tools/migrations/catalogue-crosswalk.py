"""Print renamed proof modules, matched by their immutable task IDs.

Usage: python3 tools/migrations/catalogue-crosswalk.py 51fab61e [target-commit]
The default target is the working tree. Specify both commits to recreate the
crosswalk for an archived migration. The JSON records both commit identities.
"""
import argparse
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def git(*args):
    return subprocess.check_output(["git", "-C", str(ROOT), *args])


def commit(revision):
    return git("rev-parse", "--verify", "--end-of-options", revision + "^{commit}").decode().strip()


def catalogue(revision):
    def read(name):
        path = "research/" + name
        content = git("show", f"{revision}:{path}") if revision else (ROOT / path).read_bytes()
        return json.loads(content)

    desks = {"goldbach": read("gaps.json"), **read("problems.json")}
    tasks = {}
    names = set()
    for desk, data in desks.items():
        for gap in data["gaps"]:
            ident, module = gap["id"], gap["module"]
            if ident in tasks or module.casefold() in names:
                raise ValueError(f"Duplicate task or module in {revision or 'working tree'}: {ident}")
            if gap["file"] != f"lean/{module.replace('.', '/')}.lean":
                raise ValueError(f"File and module disagree for {ident}")
            tasks[ident] = (desk, gap["statement"], module)
            names.add(module.casefold())
    return tasks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", help="commit before the namespace migration")
    parser.add_argument("target", nargs="?", help="commit after the migration (default: working tree)")
    args = parser.parse_args()
    base = commit(args.base)
    target = commit(args.target) if args.target else None
    before, after = catalogue(base), catalogue(target)
    if before.keys() != after.keys():
        raise ValueError("The two catalogues register different task IDs")
    renamed = {}
    for ident, (desk, statement, old_module) in sorted(before.items()):
        new_desk, new_statement, new_module = after[ident]
        if (desk, statement) != (new_desk, new_statement):
            raise ValueError(f"Desk or frozen statement changed for {ident}")
        if new_module != old_module:
            renamed[ident] = {"from": old_module, "to": new_module}
    print(json.dumps({"base": base, "target": target or "working tree", "renamed": renamed}, indent=2))


if __name__ == "__main__":
    main()
