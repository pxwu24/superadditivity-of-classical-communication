#!/usr/bin/env python3
"""Compare original and revised public theorem statements (proof bodies excluded)."""
from pathlib import Path
import re, json, hashlib
root = Path(__file__).resolve().parents[1]
original = root / 'verification/reference/AppendixB_original.lean'
pat = re.compile(r'^(?:lemma|theorem)\s+([^\s({:]+)([\s\S]*?)\s*:=\s*by', re.M)
def signatures(text):
    return {name: re.sub(r'\s+', '', signature) for name, signature in pat.findall(text)}
old = signatures(original.read_text())
new = signatures('\n'.join(p.read_text() for p in sorted((root / 'src/Entropy').glob('*.lean'))))
missing = sorted(set(old) - set(new))
changed = sorted(name for name in old if name in new and old[name] != new[name])
result = {'original_public_theorems': len(old), 'preserved_count': len(old)-len(missing)-len(changed),
          'missing': missing, 'changed': changed,
          'original_sha256': hashlib.sha256(original.read_bytes()).hexdigest()}
(root / 'verification/entropy_statements.json').write_text(json.dumps(result, indent=2)+'\n')
if missing or changed:
    raise SystemExit(str(result))
print(f'{len(old)} original public theorem statements preserved.')
