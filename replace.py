#!/usr/bin/env python3
"""
Symbol mapping for .v (Coq) files under the current directory.
Replace Unicode/logic symbols with ASCII equivalents (or custom strings).
Modify SYMBOL_MAP to add/change mappings.
"""

import os
from pathlib import Path

# ---------------------------------------------------------------------------
# Symbol mapping: symbol -> replacement string (modify as needed)
# ---------------------------------------------------------------------------
SYMBOL_MAP = {
    "∃": "exists",
    "∀": "forall",
    "∧": "/\\",
    "∨": "\\/",
    "→": "->",
    "↔": "<->",
    "¬": "~",
    "≠": "<>",
    "∈": "in",
    "⇒": "=>",
    "×": "*",
    "  (* FILL IN HERE *)\n": "",
    "  (* WORKED IN CLASS *)\n": "",
    "≤": "<=",
    "≥": ">=",
    # "Admitted.": "Qed.",
}


def find_v_files(root: Path) -> list[Path]:
    """Find all .v files under root (including subdirectories)."""
    return sorted(root.rglob("*.v"))


def apply_mapping(text: str, mapping: dict[str, str]) -> str:
    """Apply symbol mapping to text. Order of replacement is by key."""
    result = text
    for symbol, replacement in mapping.items():
        result = result.replace(symbol, replacement)
    return result


def process_file(path: Path, mapping: dict[str, str], dry_run: bool = False) -> bool:
    """
    Read a .v file, apply mapping, and write back (unless dry_run).
    Returns True if file was changed.
    """
    content = path.read_text(encoding="utf-8")
    new_content = apply_mapping(content, mapping)
    if content == new_content:
        return False
    if not dry_run:
        path.write_text(new_content, encoding="utf-8")
    return True


def main() -> None:
    root = Path(__file__).resolve().parent
    dry_run = "--dry-run" in os.sys.argv # first overview

    if not SYMBOL_MAP:
        print("SYMBOL_MAP is empty. Add mappings in replace.py and run again.")
        return

    v_files = find_v_files(root)

    if not v_files:
        print("No .v files found under", root)
        return

    changed = 0
    for path in v_files:
        if process_file(path, SYMBOL_MAP, dry_run = dry_run):
            changed += 1
            print("Updated" if not dry_run else "Would update", path.relative_to(root))

    mode = "Would update" if dry_run else "Updated"
    print(f"\n{mode} {changed} of {len(v_files)} .v file(s).")


if __name__ == "__main__":
    main()
