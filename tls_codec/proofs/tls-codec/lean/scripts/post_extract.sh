#!/bin/sh
cd "$(dirname "$0")/.." || exit 1

# The aeneas version string in `translation.json` depends on how the binary was
# built (e.g. `38960402` / `3896040`): normalise it to the pinned revision of
# `../../setup.sh`, so that re-extraction is byte-identical with any build.
rev=$(sed -n 's/^AENEAS_REV=\([0-9a-f]\{8\}\).*/\1/p' ../../setup.sh)
sed -i "s/^  \"aeneas_version\": \"[^\"]*\",$/  \"aeneas_version\": \"$rev\",/" translation.json

# WORKAROUND (aeneas bug):
# a generic trait method called at a type that contains a mutable borrow,
# `T::tls_deserialize::<Take<&mut R>>(&mut sub)` (the `Vec<T>`, `TlsVecU*` and
# `SecretTlsVecU*` `std` deserializers), is destructured as if it returned a
# backward function `Take R → Take R`, but the trait field (generic in `R`) returns
# only `(result, reader)`: "expected a product type, got core.io.util.Take R".
# Rust's parametricity makes that backward function the identity (the method
# cannot replace the `&mut R` inside the `Take`), so bind it as such.
# Undo: delete this block once aeneas types the call by the trait field.
f=TlsCodec/Extraction/Funs.lean
n=$(grep -c '^    let (r, sub, tls_deserialize_back) ←$' "$f")
done_n=$(grep -c '^    let tls_deserialize_back := fun (x : core.io.util.Take R) => x$' "$f")
if [ "$n" = 0 ] && [ "$done_n" = 9 ]; then
  exit 0  # already patched
fi
if [ "$n" != 9 ]; then
  echo "post_extract.sh: expected 9 'tls_deserialize_back' sites in $f, found $n" >&2
  exit 1
fi
sed -i 's/^    let (r, sub, tls_deserialize_back) ←$/    let tls_deserialize_back := fun (x : core.io.util.Take R) => x\n    let (r, sub) ←/' "$f"
