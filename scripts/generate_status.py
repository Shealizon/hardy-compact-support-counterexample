from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
ENTRY = ROOT / "HardyCompactSupport.lean"
MODULES = ROOT / "HardyCompactSupport"
STATUS = ROOT / "STATUS.md"
STATUS_JSON = ROOT / "status.json"

DECLARATION = re.compile(
    r"^\s*(theorem|lemma)\s+([A-Za-z0-9_'.]+)\b", re.MULTILINE
)


def sources() -> list[Path]:
    result = [ENTRY]
    if MODULES.exists():
        result.extend(sorted(MODULES.rglob("*.lean")))
    return result


def build() -> tuple[bool, str]:
    process = subprocess.run(
        ["lake", "build"],
        cwd=ROOT,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=600,
    )
    return process.returncode == 0, process.stdout


def declarations() -> list[dict]:
    rows = []
    for path in sources():
        text = path.read_text(encoding="utf-8")
        matches = list(DECLARATION.finditer(text))
        for index, match in enumerate(matches):
            body_end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
            body = text[match.end():body_end]
            rows.append(
                {
                    "name": match.group(2),
                    "kind": match.group(1),
                    "file": path.relative_to(ROOT).as_posix(),
                    "line": text.count("\n", 0, match.start()) + 1,
                    "complete": re.search(r"\bsorry\b", body) is None,
                }
            )
    return rows


def forbidden_imports() -> list[str]:
    violations = []
    for path in sources():
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            if re.match(r"\s*import\s+HardyEndpoint(?:\.|\s|$)", line):
                violations.append(
                    f"{path.relative_to(ROOT).as_posix()}:{line_number}: {line.strip()}"
                )
    return violations


def main() -> None:
    build_ok, output = build()
    rows = declarations()
    violations = forbidden_imports()
    complete = sum(row["complete"] for row in rows)
    result = {
        "build_ok": build_ok,
        "forbidden_old_imports": violations,
        "declaration_count": len(rows),
        "complete": complete,
        "incomplete": len(rows) - complete,
        "declarations": rows,
        "build_output": output[-4000:],
    }
    STATUS_JSON.write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    lines = [
        "# Hardy Compact Support Proof Status",
        "",
        f"- Lake build: {'OK' if build_ok else 'FAILED'}",
        f"- Imports from archived proof: {len(violations)}",
        f"- Theorems and lemmas: {len(rows)}",
        f"- Complete: {complete}",
        f"- Incomplete: {len(rows) - complete}",
        "",
        "| Status | Declaration | Location |",
        "|---|---|---|",
    ]
    for row in rows:
        status = "complete" if row["complete"] else "sorry"
        lines.append(
            f"| {status} | `{row['name']}` | "
            f"`{row['file']}:{row['line']}` |"
        )
    if violations:
        lines.extend(["", "## Forbidden imports", ""])
        lines.extend(f"- {violation}" for violation in violations)
    if not build_ok:
        lines.extend(["", "## Build output", "", "```text", output[-4000:], "```"])
    STATUS.write_text("\n".join(lines) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
