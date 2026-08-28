"""Generate reproducible SLOB fixtures for Python/Java compatibility tests."""
import json
from pathlib import Path
import slob

ROOT = Path(__file__).resolve().parents[1] / "fixtures"

def write(name, compression="lzma2", entries=(), aliases=()):
    path = ROOT / name
    with slob.create(str(path), compression=compression) as w:
        for content, keys, content_type in entries:
            w.add(content, *keys, content_type=content_type)
        for alias, target in aliases:
            w.add_alias(alias, target)
    with slob.open(str(path)) as r:
        data = {"compression": r.compression, "blob_count": r.blob_count,
                "keys": [item.key for item in r]}
    path.with_suffix(".json").write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

def main():
    ROOT.mkdir(exist_ok=True)
    text = "text/plain; charset=utf-8"
    basic = [(b"example", ("example",), text)]
    write("empty.slob", entries=[])
    write("uncompressed.slob", "", basic)
    write("zlib.slob", "zlib", basic)
    write("lzma2.slob", entries=basic)
    write("unicode.slob", entries=[("Привет, 世界".encode(), ("ёж", "世界"), text)])
    write("aliases.slob", entries=basic, aliases=[("sample", "example"), ("demo", "example")])
    write("duplicate-keys.slob", entries=[(b"first", ("same",), text), (b"second", ("same",), text)])
    write("multiple-content-types.slob", entries=[(b"<h1>x</h1>", ("html",), "text/html"), (b"body{}", ("style",), "text/css")])
    write("fragments.slob", entries=[(b"fragment", (("page", "section"),), text)])
    write("large-bin.slob", entries=[(b"x" * 1048576, ("large",), "application/octet-stream")])
    corrupted = ROOT / "corrupted"; corrupted.mkdir(exist_ok=True)
    lzma = (ROOT / "lzma2.slob").read_bytes(); zlib = (ROOT / "zlib.slob").read_bytes()
    variants = {"invalid-magic.slob": b"broken!!" + lzma[8:], "truncated-header.slob": lzma[:20],
        "truncated-ref-table.slob": lzma[:-24], "truncated-store.slob": lzma[:-1],
        "invalid-bin-index.slob": lzma, "invalid-item-index.slob": lzma, "invalid-content-type.slob": lzma,
        "unknown-compression.slob": lzma[:31] + b"abcde" + lzma[36:],
        "corrupted-zlib.slob": zlib[:-8] + b"\xff" * 8, "corrupted-lzma2.slob": lzma[:-8] + b"\xff" * 8}
    for name, data in variants.items(): (corrupted / name).write_bytes(data)

if __name__ == "__main__": main()
