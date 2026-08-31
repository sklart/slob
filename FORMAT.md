# SLOB file format

This document describes the existing SLOB v1 binary format as written by this
project.  It is descriptive: readers and writers must not change the on-disk
format merely to implement these rules.

## Conventions

All integer fields are unsigned and big-endian (network byte order).  `u8`,
`u16`, `u32`, and `u64` therefore occupy 1, 2, 4, and 8 bytes.  Text is
encoded with the header's `encoding`, except the encoding name itself, which
is UTF-8.

`tiny-text` is `u8 byte_length` followed by that many bytes.  `text` is
`u16 byte_length` followed by that many bytes.  A writer may reserve a
255-byte `tiny-text` field for an editable tag value and pad the unused bytes
with zero; readers treat the first zero in a 255-byte field as its terminator.

An **item list** is:

```
u32 count
u64 offsets[count]
item data
```

Each offset is relative to the beginning of `item data`, not to the beginning
of the file.  It is valid for item data to be in a different physical SLOB
part, but the logical concatenation is used for all offsets.

## Header

The header starts at byte zero and is followed immediately by the reference
item list.

```
8 bytes     magic = 21 2d 31 53 4c 4f 42 1f  (`!-1SLOB\x1f`)
16 bytes    UUID in RFC 4122 byte order
tiny-text   encoding name (UTF-8)
tiny-text   compression name (header encoding)
u8          tag count
repeat      tiny-text key, tiny-text value
u8          content type count
repeat      text content type
u32         number of stored blobs
u64         store offset
u64         complete logical file size
```

The declared file size must equal the logical size of all parts.  `store
offset` must point at an item-list header after the reference list and be
within that size.  The header's end is the reference-list offset.

## References, blobs, aliases, and fragments

The reference list uses the item-list layout.  A reference item is:

```
text       key
u32        bin index
u16        item index within the bin
tiny-text  fragment
```

Each reference exposes one visible blob.  Several references can target the
same `(bin index, item index)`; this represents aliases without duplicating
payload.  `fragment` is an application-level anchor (normally empty) attached
to the reference, not to the stored payload.  References are sorted using the
writer's ICU identical collation key; consumers must not assume bytewise
Unicode ordering.

## Store and bins

The store is an item list whose items are compressed bins:

```
u32        bin item count
u8[]       content-type id for each bin item
u32        compressed payload length
bytes       compressed payload
```

A content-type id indexes the header's zero-based content-type table.  After
decompression, a bin payload contains `bin item count` entries, each:

```
u32        content byte length
bytes       content
```

The bin's item directory and all item bytes must fit exactly within the
decompressed payload.  A `(bin index, item index)` in a reference must select
an existing store bin and an existing bin item.  `blob_count` is the number of
stored bin items, while the reference count may be larger due to aliases.

## Compression

The header compression name applies independently to every store bin.  The
existing writer supports the empty name (identity/no compression), `zlib`,
`bz2`, and raw `lzma2`; a reader that does not support a declared name must
reject the file.  Raw LZMA2 is not an `.xz` container.  Decompression must
consume a valid complete stream and must not expose bytes beyond the declared
bin payload.

## Required validation

Readers must reject a file when any of the following is false:

- magic, text encoding, compression name, and declared logical file size are valid;
- all header, list headers, pointer tables, and referenced item ranges are
  inside the logical file size, with overflow-safe arithmetic;
- counts fit the reader's representable collection sizes;
- every content-type id is less than the content-type count;
- every reference's bin and item index is in range;
- every bin item length and directory entry is inside the decompressed bin;
- compressed and decompressed data are complete according to the selected
  codec.

These invariants deliberately leave metadata tags and content bytes opaque to
the SLOB container format.
