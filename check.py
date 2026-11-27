"""Run the Palomar template's kernel checks for the local classical strong subadditivity pilot on Linux."""

import json
import subprocess
from pathlib import Path
from tempfile import TemporaryDirectory


def main():
    project = Path(__file__).resolve().parent
    prefix = subprocess.check_output(
        ["lean", "--print-prefix"], cwd=project, text=True
    ).strip()
    binaries = Path(prefix) / "bin"
    config = json.loads((project / "comparator.json").read_text(encoding="utf-8"))
    config["external_kernels"] = {
        "nanoda": [str(binaries / "nanoda_bin")],
        "con-ron": [str(binaries / "con-ron")],
    }
    with TemporaryDirectory() as temporary:
        config_path = Path(temporary) / "comparator.json"
        config_path.write_text(json.dumps(config), encoding="utf-8")
        subprocess.run(
            ["lake", "comparator", "--config", str(config_path)], cwd=project, check=True
        )


if __name__ == "__main__":
    main()
