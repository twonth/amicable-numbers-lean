#!/usr/bin/env python3
# Copyright (c) 2026 Paul Pollack. All rights reserved.
# Released under the MIT license as described in the file LICENSE.
# Authors: ChatGPT Astra
# Responsible maintainer: Paul Pollack
"""Validate release metadata, source links, and optionally Lean declaration names.

Requires PyYAML and jsonschema. With --lean-project, also requires the pinned
Lean toolchain and built dependencies there. This does not assess mathematical
fidelity or replace Comparator.
"""

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile
from urllib.request import urlopen

import jsonschema
import yaml

SCHEMA_REVISION = "99c678e569c7c4c0772db297c5ddd5e4c9b6322e"
SCHEMA_URL = (
    "https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/"
    + SCHEMA_REVISION + "/schema/v0.4.schema.json"
)
SCHEMA_SHA256 = "25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


class UniqueKeyLoader(yaml.SafeLoader):
    pass


def unique_mapping(loader, node, deep=False):
    result = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node, deep=deep)
        require(key not in result, f"Duplicate YAML key: {key}")
        result[key] = loader.construct_object(value_node, deep=deep)
    return result


UniqueKeyLoader.add_constructor(
    yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, unique_mapping
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--schema", type=Path, help="Offline copy of the pinned schema")
    parser.add_argument("--lean-project", type=Path, help="Compile declaration checks in this matching Lake project")
    parser.add_argument("--report", type=Path, help="Write a JSON validation report")
    args = parser.parse_args()
    repo = args.repo.resolve()
    checked = {}

    def read(relative):
        path = (repo / relative).resolve()
        require(path.is_relative_to(repo), f"Path outside repository: {relative}")
        data = path.read_bytes()
        checked[relative] = digest(data)
        return data

    schema_bytes = args.schema.read_bytes() if args.schema else urlopen(SCHEMA_URL, timeout=30).read()
    require(digest(schema_bytes) == SCHEMA_SHA256, "Schema hash differs from pinned revision")
    metadata = yaml.load(read("formalization.yaml"), Loader=UniqueKeyLoader)
    jsonschema.validate(metadata, json.loads(schema_bytes))
    alignment = metadata["alignment"]
    source = read(alignment["source_file"])
    require(digest(source) == alignment["source_sha256"], "Current manuscript hash mismatch")
    original = alignment["original_input"]
    require(digest(read(original["file"])) == original["sha256"], "Frozen input hash mismatch")
    tex = source.decode("utf-8-sig")
    tex = "\n".join(line.split("%", 1)[0] for line in tex.splitlines())
    labels = set(re.findall(r"\\label\{([^}]+)\}", tex))
    declarations, modules = set(), set()
    entries = alignment["statements"]
    for entry in entries:
        for label in [entry["source_label"], *entry.get("related_source_labels", [])]:
            require(label in labels, f"Missing TeX label: {label}")
        if "lean" in entry:
            module = entry["module"]
            text = read(module).decode("utf-8-sig")
            short_name = entry["lean"].rsplit(".", 1)[-1]
            require(re.search(r"\b(?:theorem|lemma|def|abbrev|structure)\s+" + re.escape(short_name) + r"\b", text),
                    f"Declaration {entry['lean']} not found in {module}")
            modules.add(module)
            declarations.add(entry["lean"])
            declarations.update(entry.get("related_declarations", []))
        else:
            require(entry["status"] == "not-formalized", "Missing Lean name on a formalized entry")

    hashes = json.loads(read("verification/comparator-source-hashes.json"))
    for name, sha in hashes.items():
        require(digest(read(name)) == sha, f"Comparator input has changed: {name}")
    comparator = json.loads(read("verification/comparator-status.json"))
    require(comparator["status"] == "passed", "Comparator did not pass")
    require(digest(read("verification/comparator.log")) == comparator["logSha256"], "Comparator log hash mismatch")
    config = json.loads(read("comparator.json"))
    require(config == comparator["configuration"], "Comparator configuration mismatch")
    human_review_check = "not-recorded"
    if "human_review_record" in metadata["review"]:
        review = json.loads(read(metadata["review"]["human_review_record"]))
        require(review["reviewer"] in metadata["review"]["reviewers"], "Human reviewer mismatch")
        require(review["completedOn"] == metadata["review"]["human_review_date"], "Human review date mismatch")
        require(review["scope"] == metadata["review"]["human_review_scope"], "Human review scope mismatch")
        for artifact in (review["manuscript"], review["challenge"]):
            require(digest(read(artifact["file"])) == artifact["sha256"], "Reviewed artifact has changed: " + artifact["file"])
        require(review["manuscript"]["label"] in labels, "Reviewed manuscript label missing")
        require(review["challenge"]["declaration"] in config["theorem_names"], "Reviewed challenge differs from Comparator configuration")
        human_review_check = "passed"
    for result in metadata["status"]["main_results"]:
        read(result["file"])
        require(result["axioms"] == config["permitted_axioms"], "Axiom lists disagree")
        if "comparator_config" in result:
            require(result["declaration"] in config["theorem_names"], "Result absent from Comparator configuration")

    for name in ("LICENSE", "LICENSE_SCOPE.md", "vendor-provenance.json",
                 "PrimeNumberTheoremAnd/LICENSE", "vendor-licenses/PrimeGapsLib-LICENSE",
                 "vendor-licenses/PrimeNumberTheoremAnd-LICENSE"):
        read(name)

    lean_check = "not-run"
    if args.lean_project:
        project = args.lean_project.resolve()
        for name, sha in hashes.items():
            require(digest((project / name).read_bytes()) == sha, f"Lean project differs: {name}")
        imports = sorted(name[:-5].replace("/", ".") for name in modules)
        build = subprocess.run(["lake", "build", *imports], cwd=project, text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        require(build.returncode == 0, build.stdout)
        content = "\n".join("import " + name for name in imports) + "\n\n"
        content += "\n".join("#check " + name for name in sorted(declarations)) + "\n"
        with tempfile.TemporaryDirectory(prefix="metadata-check-", dir=project) as directory:
            check_file = Path(directory) / "Check.lean"
            check_file.write_text(content, encoding="utf-8")
            run = subprocess.run(["lake", "env", "lean", str(check_file)], cwd=project,
                                 text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            require(run.returncode == 0, run.stdout)
        lean_check = "passed"

    report = {
        "status": "passed",
        "completedAtUtc": datetime.now(timezone.utc).isoformat(),
        "schema": {"version": "v0.4", "revision": SCHEMA_REVISION,
                   "url": SCHEMA_URL, "sha256": SCHEMA_SHA256},
        "checks": {"schema": "passed", "uniqueYamlKeys": "passed",
                   "manuscriptHashes": "passed", "sourceLabelsAndModulePaths": "passed",
                   "comparatorInputsAndLog": "passed", "leanDeclarationNames": lean_check,
                   "humanReviewRecordConsistency": human_review_check},
        "alignmentEntries": len(entries),
        "alignmentStatuses": dict(Counter(entry["status"] for entry in entries)),
        "uniqueLeanDeclarations": len(declarations),
        "comparatorCompletedAtUtc": comparator["completedAtUtc"],
        "inputs": checked,
        "limitations": "Structural validation and declaration existence only; no automatic assessment of mathematical correspondence. Human review, when recorded, is limited to its stated scope."
    }
    if args.report:
        args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "inputs"}, indent=2))


if __name__ == "__main__":
    main()
