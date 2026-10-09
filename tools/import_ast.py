#!/usr/bin/env python3
"""Translate the pinned literal Lean AST to HOL constructors (untrusted import).
No Lean compiler or generated Lean proof modules are needed. Unknown syntax
is rejected. HOL checks the generated terms; cross-prover agreement remains
a separate obligation, not a claim made by this importer.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
CONSTRUCTORS = {
    "Decl.decl": "Decl", "Decl.exnDecl": "ExnDecl", "Decl.function": "Function",
    "Shape.one": "One", "Shape.comb": "Comb",
    "VarKind.local": "Local", "VarKind.global": "Global",
    "BinOp.add": "Add", "BinOp.sub": "Sub", "BinOp.and": "And",
    "BinOp.or": "Or", "BinOp.xor": "Xor", "PanOp.mul": "Mul",
    "Cmp.equal": "Equal", "Cmp.notEqual": "NotEqual", "Cmp.less": "Less",
    "Cmp.notLess": "NotLess", "Cmp.lower": "Lower", "Cmp.notLower": "NotLower",
    "Shift.lsl": "Lsl", "Shift.lsr": "Lsr", "Shift.asr": "Asr",
    "OpSize.op8": "Op8", "OpSize.opW": "OpW", "PrimOp.addCarry": "AddCarry",
    "some": "SOME", "none": "NONE", "true": "T", "false": "F",
}
for lean, hol in {
    "const":"Const", "var":"Var", "rStruct":"RStruct", "rField":"RField",
    "load":"Load", "loadByte":"LoadByte", "op":"Op", "panOp":"Panop",
    "cmp":"Cmp", "shift":"Shift", "baseAddr":"BaseAddr",
}.items(): CONSTRUCTORS["Exp."+lean] = hol
for lean, hol in {
    "skip":"Skip", "dec":"Dec", "assign":"Assign", "primitive":"Primitive",
    "store":"Store", "storeByte":"StoreByte", "seq":"Seq", "ite":"If",
    "while":"While", "break":"Break", "call":"Call", "decCall":"DecCall",
    "extCall":"ExtCall", "raise":"Raise", "return":"Return",
    "shMemLoad":"ShMemLoad", "shMemStore":"ShMemStore",
}.items(): CONSTRUCTORS["Prog."+lean] = hol
FIELDS = {"name":"name", "inline":"inline", "exported":"export",
          "params":"params", "body":"body", "returnShape":"return"}
TOKEN = re.compile(r'"(?:[^"\\]|\\.)*"|[A-Za-z_][A-Za-z_0-9.]*|[0-9]+|:=|[(){}\[\],]|\s+')

def translate(body, known):
    out, stack = [], []
    tokens = []
    pos = 0
    for match in TOKEN.finditer(body):
        if match.start() != pos: raise ValueError("unknown syntax: " + body[pos:pos+60])
        pos = match.end()
        if not match.group().isspace(): tokens.append(match.group())
    if pos != len(body): raise ValueError("unparsed suffix: " + body[pos:])
    i = 0
    while i < len(tokens):
        t = tokens[i]
        if tokens[i:i+3] == ['(', 'BitVec.ofNat', '64']:
            n, closing = tokens[i+3:i+5]
            if not n.isdigit() or closing != ')' or int(n) >= 2**64:
                raise ValueError("invalid 64-bit literal")
            out.append(n+'w'); i += 5; continue
        if t.startswith('"'): out.append('«'+json.loads(t)+'»')
        elif t in CONSTRUCTORS: out.append(CONSTRUCTORS[t])
        elif t in FIELDS:
            if not stack or stack[-1] != '{' or tokens[i+1] != ':=':
                raise ValueError("unexpected record field " + t)
            out.append(('' if t == 'name' else '; ') + FIELDS[t])
        elif t in known or t.isdigit() or t == ':=': out.append(t)
        elif t in ['(', '[', '{']:
            stack.append(t); out.append('<|' if t == '{' else t)
        elif t in [')', ']', '}']:
            if not stack or stack.pop() != {')':'(', ']':'[', '}':'{'}[t]:
                raise ValueError("unbalanced AST")
            out.append('|>' if t == '}' else t)
        elif t == ',': out.append(';' if stack and stack[-1] == '[' else ',')
        else: raise ValueError("unknown token " + t)
        i += 1
    if stack: raise ValueError("unclosed AST")
    return ' '.join(out)

def generate(source):
    expected = json.loads((ROOT/'provenance.json').read_text())['ast_sha256']
    if hashlib.sha256(source).hexdigest() != expected:
        raise ValueError("AST does not match pinned provenance")
    text = source.decode().split('open Flapjack',1)[1].rsplit('end Guest',1)[0]
    decls = list(re.finditer(r'\bdef (\w+) : (Decl \(BitVec 64\)|List \(Decl \(BitVec 64\)\)) :=', text))
    if not decls or text[:decls[0].start()].strip(): raise ValueError("invalid AST header")
    known, output = set(), ['(* Generated from the pinned init-e literal AST. *)',
        'Theory initGuest', 'Ancestors panLang', 'Libs preamble', '']
    for j, m in enumerate(decls):
        name = m[1]
        if name in known: raise ValueError("duplicate declaration")
        body = text[m.end():decls[j+1].start() if j+1<len(decls) else len(text)].strip()
        body = body.replace('/-- The stateless guest as flapjack Pancake declarations. -/', '')
        term = translate(body, known)
        ty = '64 panLang$decl' + (' list' if m[2].startswith('List') else '')
        output += [f'Definition {name}_def:', f'  {name} : {ty} =', '  '+term, 'End', '']
        known.add(name)
    if decls[-1][1] != 'guestAst': raise ValueError("missing final guestAst")
    return '\n'.join(output)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = generate(args.source.read_bytes())
    target = ROOT/'challenge/initGuestScript.sml'
    if args.check:
        if target.read_text() != result: raise SystemExit("generated AST differs")
        print("Pinned AST reproduces exactly")
    else:
        target.write_text(result)
        print(f"Wrote {target}")
