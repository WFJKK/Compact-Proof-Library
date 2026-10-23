#!/usr/bin/env python3
"""Package an instance of the library as an open-lane candidate, for the acceptance service.

    python3 scripts/make_candidate.py <instance module> <out dir> --model <model> --network <network>
        --claimed <count> --bill <bill>

The acceptance service (scripts/accept.py of the Lean repository Auto-Research-Compact-Proof-in-Lean)
takes a folder with manifest.json and modules under Candidate/, which may import each other, the
protected module, CompactCheck.* and Mathlib.*. This script copies the instance (for example
instances/LinearMaxKInstances/Max2Tiny.lean) and the library modules it needs, transitively, under
Candidate/, rewrites their imports, puts the instance's declarations under the namespace
Candidate.<Entry><Instance>, and writes the manifest of a scored submission (the checker `D`, the
soundness theorem `D_sound`, the instance theorem `D_instance`, the target's proof `performance`).
Nothing else changes: the service compiles the same Lean source as the library.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
from pathlib import Path

LIB = Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^import\s+(\S+)\s*$")


def imports_of(text: str) -> list[str]:
    out = []
    for line in text.splitlines():
        s = line.strip()
        if not s or s.startswith("--"):
            continue
        m = IMPORT.match(s)
        if not m:
            break
        out.append(m.group(1))
    return out


def is_library(module: str) -> bool:
    """A module of the library itself (Common.*, LinearMaxK.*, ...): its source is in the repository.
    CompactCheck.*, Mathlib.* and the protected modules (under instances/) are not."""
    return module_path(module).is_file()


def module_path(module: str) -> Path:
    return LIB / (module.replace(".", "/") + ".lean")


def rewrite_imports(text: str) -> str:
    def fix(line: str) -> str:
        m = IMPORT.match(line.strip())
        if m and is_library(m.group(1)):
            return f"import Candidate.{m.group(1)}"
        return line
    lines = text.splitlines()
    head = []
    i = 0
    while i < len(lines) and (not lines[i].strip() or lines[i].strip().startswith("--") or IMPORT.match(lines[i].strip())):
        head.append(fix(lines[i]))
        i += 1
    return "\n".join(head + lines[i:]) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("instance", type=Path, help="the instance module, e.g. instances/LinearMaxKInstances/Max2Tiny.lean")
    ap.add_argument("out", type=Path)
    ap.add_argument("--model", required=True)
    ap.add_argument("--network", required=True)
    ap.add_argument("--claimed", type=int, required=True)
    ap.add_argument("--bill", type=int, required=True)
    args = ap.parse_args()

    inst = args.instance.resolve()
    text = inst.read_text()
    ns = re.search(r"^namespace\s+(\S+)\s*$", text, re.M)
    if not ns:
        raise SystemExit("the instance has no namespace")
    old_ns = ns.group(1)
    new_ns = "Candidate." + old_ns.replace(".", "").replace("Instances", "")
    name = new_ns.split(".", 1)[1]

    # the library modules the instance needs, transitively
    needed: list[str] = []
    todo = [m for m in imports_of(text) if is_library(m)]
    while todo:
        m = todo.pop()
        if m in needed:
            continue
        needed.append(m)
        todo.extend(x for x in imports_of(module_path(m).read_text()) if is_library(x))

    out = args.out.resolve()
    if out.exists():
        shutil.rmtree(out)
    (out / "Candidate").mkdir(parents=True)
    modules = []
    for m in sorted(needed):
        dst = out / "Candidate" / (m.replace(".", "/") + ".lean")
        dst.parent.mkdir(parents=True, exist_ok=True)
        dst.write_text(rewrite_imports(module_path(m).read_text()))
        modules.append(str(dst.relative_to(out)))
    body = rewrite_imports(text)
    body = re.sub(rf"^namespace {re.escape(old_ns)}\s*$", f"namespace {new_ns}", body, flags=re.M)
    body = re.sub(rf"^end {re.escape(old_ns)}\s*$", f"end {new_ns}", body, flags=re.M)
    (out / "Candidate" / f"{name}.lean").write_text(body)
    modules.append(f"Candidate/{name}.lean")

    manifest = {
        "schema": "open-lane-candidate-v1",
        "candidate_id": f"library-{name}".lower(),
        "model": args.model,
        "network": args.network,
        "claimed_count": args.claimed,
        "theorem": f"{new_ns}.performance",
        "modules": modules,
        "scored": {"checker": f"{new_ns}.D", "sound": f"{new_ns}.D_sound", "instance": f"{new_ns}.D_instance",
                   "certificate": [], "claimed_bill": args.bill},
    }
    (out / "manifest.json").write_text(json.dumps(manifest, indent=1) + "\n")
    print(out)


if __name__ == "__main__":
    main()
