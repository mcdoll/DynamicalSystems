import subprocess
import sys


def test_minimal_lyapunov_certificate_boundary():
    result = subprocess.run(
        [sys.executable, "tools/verify_minimal_lyapunov_certificate_boundary.py"],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "MINIMAL_LYAPUNOV_CERTIFICATE_BOUNDARY_OK" in result.stdout
