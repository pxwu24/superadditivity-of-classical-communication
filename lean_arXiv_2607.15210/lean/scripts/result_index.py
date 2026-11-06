#!/usr/bin/env python3
"""Generate the numbered result guide and complete local import closures."""
from __future__ import annotations
import argparse
import json
import re
from pathlib import Path
from verify_lean import ROOT, IMPORT, source_modules, convergence_source_index

KINDS = {'II.2':'Lemma', 'II.3':'Lemma', 'III.1':'Theorem', 'III.2':'Corollary',
         'III.3':'Lemma', 'III.4':'Lemma', 'IV.1':'Theorem', 'IV.2':'Corollary',
         'V.1':'Theorem', 'V.2':'Proposition', 'I.1':'Theorem', 'VI.1':'Proposition',
         'A.1':'Lemma', 'A.2':'Lemma', 'A.3':'Proposition', 'A.4':'Proposition',
         'B.1':'Proposition', 'B.2':'Proposition', 'C.1':'Lemma', 'C.2':'Lemma'}


def generate(include_readme=True):
    data = json.loads((ROOT / 'results/RESULTS.json').read_text())
    modules = source_modules()
    artifacts, index, declarations = {}, [], []
    for row in data['results']:
        seen = set()
        def visit(module):
            if module in seen:
                return
            if module not in modules:
                raise ValueError('Unknown local module ' + module)
            seen.add(module)
            for dep in IMPORT.findall(modules[module].read_text()):
                if dep in modules:
                    visit(dep)
        for name in row['entry_modules']:
            visit(name)
        related = [{'module': m, 'path': str(modules[m].relative_to(ROOT))}
                   for m in sorted(seen)]
        number, title = row['number'], row['title']
        filename = number.replace('.', '_') + '.md'
        kind = KINDS[number]
        status = {'complete': 'Complete',
                  'complete_under_permitted_black_box': 'Deduction verified; the block-modified strong-convergence theorem remains an input'
                 }.get(row['status'], 'Components checked; full statement unfinished')
        body = f'# {kind} {number}: {title}\n\n{status}.\n\n'
        body += row['proved_scope'] + '\n\n'
        if row['status'] == 'complete_under_permitted_black_box':
            body += ('The full unverified input and the Lean progress are stated in '
                     '[convergence proof guide](../CONVERGENCE.md).\n\n')
        body += '## Check this result\n\nFirst run `bash lean_arXiv_2607.15210/lean/verify-all.sh` from the repository root. '
        body += 'Then, from `lean_arXiv_2607.15210/lean/`, run:\n\n```sh\n'
        body += "cat > InspectResult.lean <<'LEAN'\nimport AllProofs\n\n"
        for decl in row['declarations']:
            body += '#check ' + decl + '\n#print axioms ' + decl + '\n'
            declarations.append(decl)
        body += 'LEAN\nlake env lean InspectResult.lean\nrm InspectResult.lean\n```\n\n'
        body += 'The displayed hypotheses are part of the checked statement. '
        body += 'The entry declarations include the completed paper endpoints.\n\n'
        body += '## Entry files\n\n'
        for module in row['entry_modules']:
            path = modules[module].relative_to(ROOT).as_posix()
            body += f'- [{module}](../{path})\n'
        body += '\n## All related Lean files\n\n'
        body += 'This is the complete transitive local import closure of the entry files. '
        body += 'Mathlib dependencies are pinned in `lake-manifest.json`.\n\n'
        for item in related:
            body += f'- [{item["path"]}](../{item["path"]})\n'
        body += '\n## Assumptions and dependencies\n\n'
        body += '\n'.join('- ' + x for x in row['paper_assumptions']) + '\n'
        if row['paper_dependencies']:
            body += '\nPaper dependencies: ' + ', '.join(row['paper_dependencies']) + '.\n'
        if row['missing_for_paper_statement']:
            body += '\n## Remaining proof obligations\n\n'
            body += '\n'.join('- ' + x for x in row['missing_for_paper_statement']) + '\n'
        if row['python_files']:
            body += '\n## Python checks\n\n'
            for path in row['python_files']:
                if not (ROOT.parent / path).is_file():
                    raise ValueError('Missing Python file ' + path)
                body += f'- [{Path(path).name}](../../{path})\n'
            body += '\nThe exact rational certificate is a certificate of its scalar inequalities; '
            body += 'the other numerical checks are cross-checks, not universal proofs.\n'
        artifacts[ROOT / 'results' / filename] = body
        index.append({'number': number, 'status': row['status'],
                      'declarations': row['declarations'], 'local_import_closure': related})
    artifacts[ROOT / 'verification/result_sources.json'] = json.dumps(index, indent=2) + '\n'
    artifacts[ROOT / 'verification/convergence_sources.json'] = convergence_source_index(modules)
    if include_readme:
        readme = (ROOT.parent / 'readme.md').read_text()
        for marker, status in [('RESULT_TABLE', 'complete'),
                               ('CONDITIONAL_TABLE', 'complete_under_permitted_black_box')]:
            table = '| Paper result | Verified statement |\n| --- | --- |\n'
            for row in data['results']:
                number = row['number']
                if row['status'] == status:
                    title = row['title']
                    if number == 'VI.1':
                        title = 'Dimension-182 finite-channel consequence of the certified gap'
                elif marker == 'RESULT_TABLE' and number == 'VI.1':
                    title = 'Dimension-182 spectral/body certificate (exact entropy gap)'
                else:
                    continue
                table += (f"| [{KINDS[number]} {number}](lean/results/{number.replace('.', '_')}.md) | "
                          f"{title} |\n")
            if marker == 'CONDITIONAL_TABLE' and not any(
                    row['status'] == status for row in data['results']):
                table = ''
            pattern = f'<!-- {marker}_START -->.*?<!-- {marker}_END -->'
            readme, matches = re.subn(pattern,
                f'<!-- {marker}_START -->\n' + table + f'<!-- {marker}_END -->',
                readme, flags=re.S)
            if matches != 1:
                raise ValueError('README must contain exactly one ' + marker + ' marker pair')
        artifacts[ROOT.parent / 'readme.md'] = readme
    artifacts[ROOT / 'src/Checks/ResultChecks.lean'] = ('import AllProofs\n\n'
        + '\n'.join('#check ' + name for name in dict.fromkeys(declarations)) + '\n')
    return artifacts


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--no-readme', action='store_true', help='Regenerate guides without editing README prose or tables')
    args = parser.parse_args()
    for path, content in generate(include_readme=not args.no_readme).items():
        if args.check:
            if not path.is_file() or path.read_text() != content:
                raise SystemExit('Result index is stale: ' + str(path.relative_to(ROOT.parent)))
        else:
            path.parent.mkdir(exist_ok=True)
            path.write_text(content)
    print('Numbered result index and complete import closures checked.' if args.check else
          'Numbered result index and complete import closures generated.')
