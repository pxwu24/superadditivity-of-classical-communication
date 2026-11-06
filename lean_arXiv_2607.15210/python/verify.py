#!/usr/bin/env python3
"""Run the numerical checks and exact finite arithmetic certificates."""
import json
from pathlib import Path
import subprocess
import sys
import time
import hashlib

ROOT = Path(__file__).resolve().parent
P = ROOT


def run():
    logs = ROOT/'verification/python_logs'
    logs.mkdir(parents=True, exist_ok=True)
    status_file = ROOT/'verification/python_verification.json'
    status_file.write_text(json.dumps({'status': 'running'})+'\n')
    cases = [
        ('compression', P/'random_compression', ['random_compression_check.py', '--output', 'random_compression_results.json']),
        ('entropy', P/'entropy', ['verify_entropy.py', '--output', 'python_results.json']),
        ('tensor', P/'entropy', ['verify_tensor_spectra.py', '--output', 'tensor_spectra_results.json']),
        ('bell', P/'bell_output', ['verify_bell_limit.py']),
        ('main', P/'nonadditivity', ['verify_main_coefficient.py']),
        ('k182', P/'dimension_182', ['certify_k182_exact.py', '--json', 'certificate_results.json']),
        ('k182_optimized_python', P/'dimension_182', ['-O', 'certify_k182_exact.py']),
        ('finite_haar_moments', P/'haar_moments',
         ['exact_haar_moments.py', '--output', 'exact_haar_moments_results.json'])]
    records = []
    for name, cwd, args in cases:
        start = time.monotonic()
        with (logs/(name+'.log')).open('w') as handle:
            result = subprocess.run([sys.executable]+args, cwd=cwd,
                                    stdout=handle, stderr=subprocess.STDOUT)
        if result.returncode:
            status_file.write_text(json.dumps({'status': 'failed', 'check': name})+'\n')
            raise RuntimeError(f'{name} failed; see {logs/(name+".log")}')
        print('Passed', name, flush=True)
        records.append({'check': name, 'exit_code': result.returncode,
                        'source': str((cwd/next(a for a in args if a.endswith('.py'))).relative_to(ROOT)),
                        'source_sha256': hashlib.sha256((cwd/next(a for a in args if a.endswith('.py'))).read_bytes()).hexdigest(),
                        'seconds': round(time.monotonic()-start, 3)})
    summary = {'status': 'pass', 'checks': records,
               'scope': 'Exact k182 scalar certificate and finite rational Haar moment checks; numerical checks do not prove general asymptotic convergence.'}
    status_file.write_text(json.dumps(summary, indent=2)+'\n')


if __name__ == '__main__':
    run()
