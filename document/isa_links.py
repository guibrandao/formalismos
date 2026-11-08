#!/usr/bin/env python3
"""Generate isa-links.tex: one \\isadef{name}{url} per Isabelle fact cited with \\isa{...}.

Each URL points to the line of the theory file (on GitHub) where the fact is stated.
Rerun after changing the theories:  python3 isa_links.py
"""
import re
import sys
from pathlib import Path

REPO = "https://github.com/guibrandao/formalismos/blob/main"
HERE = Path(__file__).resolve().parent
THYS = HERE.parent / "thys"
TEX = HERE / "Formalismos Matemáticos.tex"
OUT = HERE / "isa-links.tex"

KEYWORDS = (r"lemma|theorem|corollary|proposition|definition|abbreviation|fun|function|"
            r"primrec|inductive|inductive_set|locale|datatype|type_synonym")
DECL = re.compile(rf"^\s*(?:{KEYWORDS})\s+([A-Za-z][A-Za-z0-9_']*)")

cited = sorted(set(re.findall(r"\\isa\{([^}]*)\}", TEX.read_text(encoding="utf8"))))

found = {}
for thy in sorted(THYS.glob("*.thy")):
    for n, line in enumerate(thy.read_text(encoding="utf8").splitlines(), start=1):
        m = DECL.match(line)
        if m and m.group(1) not in found:
            found[m.group(1)] = (thy.name, n)

lines = ["% Gerado por isa_links.py -- não edite à mão."]
for name in cited:
    if name in found:
        f, n = found[name]
        lines.append(f"\\isadef{{{name}}}{{{REPO}/thys/{f}\\#L{n}}}")
    else:
        print(f"aviso: '{name}' não encontrado nas teorias (sem link)", file=sys.stderr)
OUT.write_text("\n".join(lines) + "\n", encoding="utf8")
print(f"{len(lines) - 1} links escritos em {OUT.name}")
