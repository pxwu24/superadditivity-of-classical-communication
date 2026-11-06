#!/usr/bin/env python3
"""Distinguish checked deductions from unconditional paper verification."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--require-complete', action='store_true',
                    help='Require all indexed deductions to be checked under their stated hypotheses')
parser.add_argument('--require-unconditional', action='store_true',
                    help='Fail while any indexed result still depends on an unverified input')
args = parser.parse_args()
data = json.loads((ROOT / 'results/RESULTS.json').read_text())
remaining = [r['number'] for r in data['results']
             if r['status'] not in {'complete', 'complete_under_permitted_black_box'}]
conditional = [r['number'] for r in data['results']
               if r['status'] == 'complete_under_permitted_black_box']
progress = json.loads((ROOT / 'partial_progress/status.json').read_text())
input_removed = progress['paper_convergence_hypothesis_removed']
# Completion is supported by the current kernel audit, not just a status flag.
required = progress.get('proved_input_declarations', [])
verification = json.loads((ROOT / 'verification/verification_status.json').read_text())
audit = (ROOT / 'verification/axiom_audit.log').read_text()
audited = set(line.removeprefix('AUDIT_DECLARATION ') for line in audit.splitlines()
              if line.startswith('AUDIT_DECLARATION '))
records = verification.get('modules', [])
source_snapshot_current = (verification.get('status') == 'pass'
    and {row['path'] for row in records} ==
        {str(path.relative_to(ROOT)) for path in (ROOT / 'lean').rglob('*.lean')}
    and all((ROOT / row['path']).is_file() and
            hashlib.sha256((ROOT / row['path']).read_bytes()).hexdigest() == row['sha256']
            for row in records))
input_proof_checked = bool(required) and set(required) <= audited and source_snapshot_current
unconditional = (not remaining and input_removed
                 and progress['general_block_modified_strong_convergence_proved']
                 and input_proof_checked)
result = {
    'all_indexed_deductions_verified_under_stated_hypotheses': not remaining,
    'all_requested_paper_results_complete': unconditional,
    'unconditional_paper_verification_complete': unconditional,
    'unfinished_deductions': remaining,
    'results_depending_on_unverified_convergence_input': conditional,
    'remaining_input': None if unconditional else progress['remaining_hypothesis'],
    'convergence_input_kernel_checked': input_proof_checked,
    'source_snapshot_current': source_snapshot_current,
    'proved_input_declarations': required,
    'input_statement_and_partial_progress': '../partial_progress/README.md',
    'only_permitted_external_assumption': data['only_permitted_external_assumption'],
    'note': ('The block-modified strong-convergence theorem is proved and included in the current kernel audit.'
             if unconditional else
             'Compilation of conditional deductions does not discharge the strong-convergence hypothesis.')}
(ROOT / 'verification/paper_coverage.json').write_text(json.dumps(result, indent=2) + '\n')
if remaining:
    print('Unfinished indexed deductions:', ', '.join(remaining))
    if args.require_complete or args.require_unconditional:
        raise SystemExit(2)
else:
    print('All indexed deductions are checked under their stated hypotheses.')
if not unconditional:
    print('Unconditional verification is incomplete or its convergence proof has not passed the current audit.')
    if args.require_unconditional:
        raise SystemExit(2)
