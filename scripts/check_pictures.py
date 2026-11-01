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

Usage: check_pictures.py FOLDER...
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


def main(folders):
    """Check every .svg file in the folders. Exit 1 if any has a problem."""
    bad = False
    for folder in folders:
        for path in sorted(pathlib.Path(folder).rglob("*")):
            if not path.is_file():
                continue
            found = problems(path) if path.suffix.lower() == ".svg" else ["is not an .svg file"]
            for p in found:
                print(f"{path}: {p}")
                bad = True
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
