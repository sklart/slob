"""Generate reproducible SLOB fixtures for Python/Java compatibility tests."""
import json
import hashlib
import struct
import uuid
from pathlib import Path
import slob

ROOT = Path(__file__).resolve().parents[1] / "fixtures"

def write(name, compression="lzma2", entries=(), aliases=()):
    path = ROOT / name
    path.unlink(missing_ok=True)
    with slob.create(str(path), compression=compression) as w:
        w.tag("created.at", "2000-01-01T00:00:00+00:00")
        w.tag("version.python", "compatibility-corpus")
        w.tag("version.pyicu", "compatibility-corpus")
        w.tag("version.icu", "compatibility-corpus")
        for content, keys, content_type in entries:
            w.add(content, *keys, content_type=content_type)
        for alias, target in aliases:
            w.add_alias(alias, target)
    with path.open("r+b") as fixture:
        fixture.seek(len(slob.MAGIC))
        fixture.write(uuid.uuid5(uuid.NAMESPACE_URL, "https://slob-format.org/corpus/" + name).bytes)
    with slob.open(str(path)) as r:
        refs = []
        payload_sha256 = {}
        content_types = []
        for item in r:
            content_type = item.content_type
            refs.append({"key": item.key, "id": item.id, "fragment": item.fragment})
            payload_sha256[str(item.id)] = hashlib.sha256(item.content).hexdigest()
            if content_type not in content_types:
                content_types.append(content_type)
        data = {
            "compression": r.compression,
            "blob_count": r.blob_count,
            "refs": refs,
            "keys": [item["key"] for item in refs],
            "content_types": content_types,
            "payload_sha256": payload_sha256,
        }
    with path.with_suffix(".json").open("w", encoding="utf-8", newline="\n") as manifest:
        json.dump(data, manifest, ensure_ascii=False, indent=2)
        manifest.write("\n")

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
    invalid_bin_index = bytearray(lzma)
    invalid_item_index = bytearray(lzma)
    invalid_content_type = bytearray(lzma)
    header = header_offsets(lzma)
    ref_offset = item_offset(lzma, header["refs_offset"])
    key_length = struct.unpack_from(">H", lzma, ref_offset)[0]
    bin_index_offset = ref_offset + 2 + key_length
    store_count = struct.unpack_from(">I", lzma, header["store_offset"])[0]
    struct.pack_into(">I", invalid_bin_index, bin_index_offset, store_count)
    struct.pack_into(">H", invalid_item_index, bin_index_offset + 4, 0xffff)
    first_store_item = item_offset(lzma, header["store_offset"])
    struct.pack_into(">B", invalid_content_type, first_store_item + 4, 0xff)
    variants = {"invalid-magic.slob": b"broken!!" + lzma[8:], "truncated-header.slob": lzma[:20],
        "truncated-ref-table.slob": lzma[:-24], "truncated-store.slob": lzma[:-1],
        "invalid-bin-index.slob": invalid_bin_index, "invalid-item-index.slob": invalid_item_index,
        "invalid-content-type.slob": invalid_content_type,
        "unknown-compression.slob": lzma[:31] + b"abcde" + lzma[36:],
        "corrupted-zlib.slob": zlib[:-8] + b"\xff" * 8, "corrupted-lzma2.slob": lzma[:-8] + b"\xff" * 8}
    for name, data in variants.items(): (corrupted / name).write_bytes(data)


def header_offsets(data):
    """Return offsets needed to corrupt a generated SLOB without changing its size."""
    position = 8 + 16
    position += 1 + data[position]
    position += 1 + data[position]
    tag_count = data[position]
    position += 1
    for _ in range(tag_count):
        position += 1 + data[position]
        position += 1 + data[position]
    content_type_count = data[position]
    position += 1
    for _ in range(content_type_count):
        length = struct.unpack_from(">H", data, position)[0]
        position += 2 + length
    position += 4
    store_offset = struct.unpack_from(">Q", data, position)[0]
    position += 16
    return {"store_offset": store_offset, "refs_offset": position}


def item_offset(data, list_offset):
    count = struct.unpack_from(">I", data, list_offset)[0]
    if not count:
        raise ValueError("fixture must contain an item")
    relative_offset = struct.unpack_from(">Q", data, list_offset + 4)[0]
    return list_offset + 4 + count * 8 + relative_offset

if __name__ == "__main__": main()
