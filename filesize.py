#!/usr/bin/env python3
# Note this was written by AI and reviewed by me. Be careful.

import argparse
from pathlib import Path


def strip_comments(text: str, language: str) -> str:
    """
    Remove comments while:
      - preserving newlines, so line counting remains correct
      - preserving strings
      - supporting nested block comments

    Lean:
      -- line comment
      /- block comment -/

    Isabelle:
      (* block comment *)
    """

    if language == "lean":
        line_comment = "--"
        block_start = "/-"
        block_end = "-/"
    elif language == "isabelle":
        line_comment = None
        block_start = "(*"
        block_end = "*)"
    else:
        raise ValueError(f"Unknown language: {language}")

    result = []
    i = 0
    n = len(text)

    block_depth = 0
    in_string = False
    escaped = False

    while i < n:

        # --------------------------------------------------
        # Inside a block comment
        # --------------------------------------------------
        if block_depth > 0:
            if text.startswith(block_start, i):
                block_depth += 1
                i += len(block_start)

            elif text.startswith(block_end, i):
                block_depth -= 1
                i += len(block_end)

            else:
                # Preserve newlines for correct line numbers/counts.
                if text[i] == "\n":
                    result.append("\n")

                i += 1

            continue

        # --------------------------------------------------
        # Inside a quoted string
        # --------------------------------------------------
        if in_string:
            result.append(text[i])

            if escaped:
                escaped = False

            elif text[i] == "\\":
                escaped = True

            elif text[i] == '"':
                in_string = False

            i += 1
            continue

        # --------------------------------------------------
        # Beginning of string
        # --------------------------------------------------
        if text[i] == '"':
            in_string = True
            result.append(text[i])
            i += 1
            continue

        # --------------------------------------------------
        # Lean line comment
        # --------------------------------------------------
        if line_comment and text.startswith(line_comment, i):
            i += len(line_comment)

            # Skip until newline, but preserve the newline.
            while i < n and text[i] != "\n":
                i += 1

            continue

        # --------------------------------------------------
        # Block comment
        # --------------------------------------------------
        if text.startswith(block_start, i):
            block_depth = 1
            i += len(block_start)
            continue

        # --------------------------------------------------
        # Ordinary character
        # --------------------------------------------------
        result.append(text[i])
        i += 1

    return "".join(result)


def analyse_file(path: Path, language: str):
    # utf-8-sig also transparently removes a UTF-8 BOM if present.
    text = path.read_text(encoding="utf-8-sig")

    uncommented = strip_comments(text, language)

    # (a) Lines containing actual non-whitespace content after
    # comments have been removed.
    non_comment_lines = sum(
        1 for line in uncommented.splitlines()
        if line.strip()
    )

    # (b) UTF-8 byte count of everything except comments.
    size_without_comments = len(uncommented.encode("utf-8"))

    return non_comment_lines, size_without_comments


def analyse_directory(directory: Path, language: str):
    if language == "lean":
        extension = ".lean"
    else:
        extension = ".thy"

    # Recursively find all matching source files.
    files = sorted(directory.rglob(f"*{extension}"))

    if not files:
        print(f"No {extension} files found in {directory}")
        return

    total_lines = 0
    total_size = 0

    print(f"Directory: {directory}")
    print(f"Language: {language}")
    print(f"Files found: {len(files)}")
    print()

    for path in files:
        lines, size = analyse_file(path, language)

        total_lines += lines
        total_size += size

        # Show path relative to the supplied directory.
        relative_path = path.relative_to(directory)

        print(f"File: {relative_path}")
        print(f"  Non-comment lines: {lines}")
        print(f"  Size excluding comments: {size} bytes")
        print()

    print("=" * 50)
    print("TOTAL")
    print(f"Files: {len(files)}")
    print(f"Non-comment lines: {total_lines}")
    print(f"Size excluding comments: {total_size} bytes")


def main():
    parser = argparse.ArgumentParser(
        description="Measure Lean/Isabelle source code excluding comments."
    )

    parser.add_argument(
        "path",
        help="Lean/Isabelle source file or directory"
    )

    parser.add_argument(
        "language",
        choices=["lean", "isabelle"],
        help="Source language"
    )

    args = parser.parse_args()

    path = Path(args.path)

    if not path.exists():
        parser.error(f"Path does not exist: {path}")

    if path.is_file():
        # Original single-file behaviour.
        lines, size = analyse_file(path, args.language)

        print(f"File: {path}")
        print(f"Language: {args.language}")
        print(f"Non-comment lines: {lines}")
        print(f"Size excluding comments: {size} bytes")

    elif path.is_dir():
        analyse_directory(path, args.language)

    else:
        parser.error(f"Path is neither a file nor a directory: {path}")


if __name__ == "__main__":
    main()