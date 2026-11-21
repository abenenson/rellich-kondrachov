"""Fetch the pinned Mathlib cache for the Euclidean library and its verification files."""

from pathlib import Path
import re
import subprocess


def mathlib_imports():
    root = Path(__file__).resolve().parent.parent
    pending = [
        root / "RellichKondrachov.lean",
        root / "RellichKondrachovExamples/DownstreamCompatibility.lean",
        root / "scripts/CheckEuclidean.lean",
    ]
    visited = set()
    mathlib = set()
    pattern = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+([\w.]+)", re.MULTILINE)
    while pending:
        source = pending.pop()
        if source in visited:
            continue
        visited.add(source)
        for module in pattern.findall(source.read_text(encoding="utf-8")):
            if module.startswith("Mathlib."):
                mathlib.add(module)
            elif module.split(".")[0] == "RellichKondrachov":
                pending.append(root / Path(*module.split(".")).with_suffix(".lean"))
    return sorted(mathlib)


if __name__ == "__main__":
    subprocess.run(["lake", "exe", "cache", "get", *mathlib_imports()], check=True)
