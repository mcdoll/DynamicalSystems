#!/usr/bin/env python3
import json
from pathlib import Path

artifacts = sorted(Path("artifacts/dynamics").glob("minimal_lyapunov_certificate_example_*.json"))
assert artifacts, "missing minimal Lyapunov certificate artifact"

data = json.loads(artifacts[-1].read_text())

assert data["status"] == "MINIMAL_EXAMPLE_REEXPORT_ONLY"
assert data["lean_module"] == "DynamicalSystems.Stability.MinimalCertificate"

closed = set(data["closed_objects"])
assert "DynamicalSystems.minimalLyapunovCertificate_linear_decay" in closed
assert "DynamicalSystems.minimalLyapunovCertificate_linear_decay_stable" in closed

not_proven = set(data["not_proven"])
required_boundaries = {
    "new stability theorem",
    "global stability for arbitrary nonlinear systems",
    "global asymptotic stability for arbitrary nonlinear systems",
    "exponential stability",
    "converse Lyapunov theorem",
    "LaSalle theorem generalization",
    "mathlib upstream acceptance",
    "control-theory maintainership resolution",
    "new applied-dynamics result",
}
missing = required_boundaries - not_proven
assert not missing, f"missing boundary tokens: {sorted(missing)}"

for field in ("proves", "closed_objects"):
    text = " ".join(data[field]).lower()
    forbidden = [
        "arbitrary nonlinear",
        "converse lyapunov",
        "exponential stability",
        "new applied-dynamics result",
        "mathlib upstream acceptance",
    ]
    bad = [token for token in forbidden if token in text]
    assert not bad, f"overclaim in {field}: {bad}"

print("MINIMAL_LYAPUNOV_CERTIFICATE_BOUNDARY_OK")
