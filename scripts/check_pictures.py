#!/usr/bin/env python3
"""Check the Pictures (SVG files) that the DM writes.

An SVG file can carry code or load things from other sites. The page shows
Pictures only through <img> tags, and the server sends a strict CSP. This
script is a third guard. It fails if any SVG file in the given folders:

- has a DOCTYPE or an ENTITY declaration,
- is not well-formed XML,
- has a script, foreignObject, iframe, object, embed, or a element,
- has an animate, set, or animateTransform element that changes an
  event handler (on...) or a link (href),
- has an attribute whose name starts with "on", such as onload,
- has an href or xlink:href that does not start with "#",
- has CSS with url(...) to anything but "#...", or with @import or expression(.

It also fails on any file in the folders that is not an .svg file, because the
server would serve it (an .html or .js file could run code).

A path can also be one file. The game server checks each Picture of a live
Adventure this way before it serves it.

Exit codes: 0 if every file passes, 1 if a file is rejected, and 2 if the check could not
run (no path given, a path that does not exist, or an error in this script). The game server
records a Picture as refused only on exit code 1.

Usage: check_pictures.py FOLDER_OR_FILE...
"""

import pathlib
import re
import sys
import xml.etree.ElementTree as ET

BAD_ELEMENTS = {"script", "foreignobject", "iframe", "object", "embed", "a"}
ANIMATIONS = {"animate", "set", "animatetransform"}
CSS_URL = re.compile(r"url\(\s*['\"]?\s*([^'\")\s]*)", re.IGNORECASE)


def local(name):
    """The name without its namespace, in lowercase."""
    return name.rsplit("}", 1)[-1].rsplit(":", 1)[-1].lower()


def css_problems(css):
    """Problems in a piece of CSS."""
    found = []
    low = css.lower()
    if "@import" in low or "expression(" in low:
        found.append("CSS with @import or expression(")
    for target in CSS_URL.findall(css):
        if not target.startswith("#"):
            found.append(f"CSS url() to {target!r}")
    return found


def problems(path):
    """All problems in one SVG file."""
    raw = path.read_text(encoding="utf-8", errors="replace")
    if re.search(r"<!\s*(doctype|entity)", raw, re.IGNORECASE):
        return ["has a DOCTYPE or ENTITY declaration"]
    try:
        root = ET.fromstring(raw)
    except ET.ParseError as e:
        return [f"is not well-formed XML: {e}"]
    found = []
    for el in root.iter():
        tag = local(el.tag)
        attrs = {local(k): v for k, v in el.attrib.items()}
        if tag in BAD_ELEMENTS:
            found.append(f"has a <{tag}> element")
        if tag in ANIMATIONS:
            target = attrs.get("attributename", "").strip().lower()
            if target.startswith("on") or local(target) == "href":
                found.append(f"<{tag}> changes {target!r}")
        if tag == "style":
            found += css_problems(el.text or "")
        for name, value in attrs.items():
            if name.startswith("on"):
                found.append(f"has an event handler {name!r}")
            if name == "href" and not value.strip().startswith("#"):
                found.append(f"links to {value!r}")
            if name == "style":
                found += css_problems(value)
    return found


def files(arg):
    """The files to check for one argument: the file itself, or every file in a folder."""
    path = pathlib.Path(arg)
    if path.is_file():
        return [path]
    if not path.is_dir():
        print(f"{arg}: no such file or folder")
        return None
    return [p for p in sorted(path.rglob("*")) if p.is_file()]


REJECTED = 1
CANNOT_CHECK = 2


def main(args):
    """Check every .svg file in the folders and files. Return 1 if any has a problem, and 2 if a
    path does not exist or no path is given."""
    if not args:
        print("usage: check_pictures.py FOLDER_OR_FILE...")
        return CANNOT_CHECK
    bad = False
    for arg in args:
        found_files = files(arg)
        if found_files is None:
            return CANNOT_CHECK
        for path in found_files:
            found = problems(path) if path.suffix.lower() == ".svg" else ["is not an .svg file"]
            for p in found:
                print(f"{path}: {p}")
                bad = True
    return REJECTED if bad else 0


if __name__ == "__main__":
    try:
        code = main(sys.argv[1:])
    except Exception as e:  # noqa: BLE001 - any error means the check did not run to the end
        print(f"the check could not run: {type(e).__name__}: {e}")
        code = CANNOT_CHECK
    sys.exit(code)
